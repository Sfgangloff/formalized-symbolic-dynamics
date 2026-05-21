"""Unit tests for the ontology pipeline (Milestone 1).

Deterministic only — no network, no model. Network-facing functions are
exercised with injected fake fetchers.
"""

from __future__ import annotations

import json
from pathlib import Path

from ontology.dedup import ConservativeJudge, plan_merge
from ontology.embed import HashingEmbedder, cosine_topk
from ontology.extract import extract_paper, validate_subgraph
from ontology.formalize import next_targets, topo_order
from ontology.harvest import KeywordRelevanceScorer, build_shards, run_harvest
from ontology.lints import run_lints
from ontology.merge import apply_plan, load_subgraph
from ontology.normalize import content_hash, normalize_latex, structural_sig
from ontology.schema import Edge, EdgeType, Node, NodeKind, edge_id, node_id
from ontology.store import Store

SAMPLE_TEX = r"""
\newtheorem{thm}{Theorem}
\newtheorem{lem}{Lemma}
\newtheorem{dfn}{Definition}

\section{Subshifts}
\begin{dfn}\label{def:sft}
A subshift $X \subseteq A^{\mathbb{Z}^d}$ is of finite type.
\end{dfn}

\begin{lem}\label{lem:aux}
Every SFT (Definition~\ref{def:sft}) has a transfer matrix.
\end{lem}

\begin{thm}[Main]\label{thm:main}
For any SFT as in \ref{def:sft}, entropy is computable.
\end{thm}
\begin{proof}
By Lemma~\ref{lem:aux} and \cite{HM2007} the claim follows.
\end{proof}
"""

ATOM = """<?xml version="1.0"?>
<feed xmlns="http://www.w3.org/2005/Atom">
 <entry>
  <id>http://arxiv.org/abs/0703206v1</id>
  <title>A characterization of the entropies of multidimensional SFT</title>
  <summary>We study subshift of finite type entropy and sofic shifts.</summary>
  <published>2007-03-01T00:00:00Z</published>
  <author><name>M. Hochman</name></author>
  <author><name>T. Meyerovitch</name></author>
  <category term="math.DS"/>
 </entry>
</feed>"""


# -- schema ---------------------------------------------------------------

def test_node_edge_roundtrip():
    n = Node(id="theorem:x", kind=NodeKind.THEOREM.value, name="Main",
             tags=["sft"], hypotheses=["finite alphabet"])
    assert Node.from_dict(n.to_dict()).to_dict() == n.to_dict()
    e = Edge(id="e:1", type=EdgeType.DEPENDS_ON.value, src="a", dst="b",
             where_="in_statement")
    assert Edge.from_dict(e.to_dict()).to_dict() == e.to_dict()


def test_ids_are_deterministic():
    assert node_id(NodeKind.THEOREM, "foo") == node_id(NodeKind.THEOREM, "foo")
    assert node_id(NodeKind.THEOREM, "foo") != node_id(NodeKind.LEMMA, "foo")
    assert node_id(NodeKind.CONCEPT, "topological-entropy") == \
        "concept:topological-entropy"
    assert edge_id(EdgeType.CITES, "a", "b") == edge_id(EdgeType.CITES, "a", "b")


# -- normalize ------------------------------------------------------------

def test_normalize_idempotent_and_lexicon():
    a = normalize_latex(r"$X \subseteq A^{\mathbb{Z}^d}$  ")
    assert normalize_latex(a) == a
    assert "ℤ" in a and "⊆" in a
    # genuinely-cosmetic differences (delimiters, \mathbb braces, spacing
    # macro, formatting wrapper) collapse; author spacing need not (the
    # normalizer is deliberately conservative — it under-merges).
    h1 = content_hash("Theorem", r"$X \subseteq \mathbb{Z}$")
    h2 = content_hash("Theorem", r"\mathbf{X} \subseteq \mathbb Z \,")
    assert h1 == h2 and h1 != ""
    assert content_hash("Theorem", "") == ""


def test_structural_sig_arity_sensitive():
    s1 = structural_sig("Theorem", ["sft"], ["h1"], ["d>=2"])
    s2 = structural_sig("Theorem", ["sft"], ["h1", "h2"], ["d>=2"])
    assert s1 != s2


# -- store ----------------------------------------------------------------

def test_store_roundtrip_and_build(tmp_path: Path):
    s = Store.load(tmp_path)
    s.nodes["theorem:a"] = Node(id="theorem:a", kind=NodeKind.THEOREM.value,
                                name="A", statement_text="foo")
    s.save("run-test")
    h1 = s.snapshot_hash()
    assert h1
    s2 = Store.load(tmp_path)
    assert "theorem:a" in s2.nodes
    assert s2.snapshot_hash() == h1            # stable serialization
    assert s2.is_build_stale()
    s2.build()
    assert not s2.is_build_stale()
    (tmp_path / "build" / "ontology.db").exists()


# -- harvest --------------------------------------------------------------

def test_relevance_scorer():
    sc = KeywordRelevanceScorer()
    assert sc.score("On subshifts of finite type", "tilings and entropy") == 3
    assert sc.score("Cellular automata in biology", "no dynamics here") == 1
    assert sc.score("A paper about elliptic curves", "number theory") == 0


def test_harvest_with_fake_fetch(tmp_path: Path):
    s = Store.load(tmp_path)
    added = build_shards(s, year_from=2007)
    assert added == len(s.shards) > 0
    summary = run_harvest(
        s, fetch=lambda url: ATOM.encode(), max_shards=1, delay=0.0,
        log=lambda *_: None,
    )
    assert summary["shards_processed"] == 1
    assert s.papers  # at least the HM paper kept
    p = next(iter(s.papers.values()))
    assert p.relevance >= 2 and p.year == 2007


# -- extract --------------------------------------------------------------

def test_extract_envs_labels_refs():
    sg = extract_paper("arxiv:test", SAMPLE_TEX, "run-x")
    kinds = {n["kind"] for n in sg["nodes"]}
    assert {"Definition", "Lemma", "Theorem"} <= kinds
    assert validate_subgraph(sg) == []
    # the proof's \ref{lem:aux} -> in_proof depends_on edge on thm:main
    dep = [e for e in sg["edges"]
           if e["type"] == "depends_on" and e["where_"] == "in_proof"]
    assert dep, "proof-ref dependency not captured"
    # in-statement ref from lemma -> definition
    instmt = [e for e in sg["edges"]
              if e["type"] == "depends_on" and e["where_"] == "in_statement"]
    assert instmt
    assert sg["citations"], "cite key not collected"


# -- dedup / merge --------------------------------------------------------

def test_merge_dedup_and_idempotent(tmp_path: Path):
    s = Store.load(tmp_path)
    sg = extract_paper("arxiv:p1", SAMPLE_TEX, "run-1")
    nodes = [Node.from_dict(n) for n in sg["nodes"]]
    edges = [Edge.from_dict(e) for e in sg["edges"]]

    plan = plan_merge(s, nodes, judge=ConservativeJudge())
    r1 = apply_plan(s, "arxiv:p1", nodes, edges, plan, run_id="run-1",
                    reviews_dir=tmp_path / "reviews")
    assert r1["added_nodes"] == len(nodes)
    n_nodes, n_edges = len(s.nodes), len(s.edges)

    # re-running the same paper changes nothing (idempotent §1.5)
    plan2 = plan_merge(s, nodes, judge=ConservativeJudge())
    apply_plan(s, "arxiv:p1", nodes, edges, plan2, run_id="run-2",
               reviews_dir=tmp_path / "reviews")
    assert len(s.nodes) == n_nodes and len(s.edges) == n_edges


def test_in_statement_beats_in_proof_on_collision(tmp_path: Path):
    # same pair (thm -> def) referenced in BOTH the statement and the
    # proof must collapse to one edge whose where_ is in_statement, and
    # the result must not depend on insertion order (Phase E ordering).
    tex = (
        r"\newtheorem{thm}{Theorem}" "\n"
        r"\newtheorem{dfn}{Definition}" "\n"
        r"\begin{dfn}\label{d}A subshift is SFT.\end{dfn}" "\n"
        r"\begin{thm}\label{t}SFT (\ref{d}) has computable entropy.\end{thm}"
        "\n\\begin{proof}By \\ref{d}.\\end{proof}\n"
    )
    s = Store.load(tmp_path)
    sg = extract_paper("arxiv:c", tex, "r")
    nodes = [Node.from_dict(n) for n in sg["nodes"]]
    edges = [Edge.from_dict(e) for e in sg["edges"]]
    plan = plan_merge(s, nodes, judge=ConservativeJudge())
    apply_plan(s, "arxiv:c", nodes, edges, plan, run_id="r",
               reviews_dir=tmp_path / "reviews")
    deps = [e for e in s.edges.values() if e.type == "depends_on"]
    assert len(deps) == 1 and deps[0].where_ == "in_statement"


def test_l0_exact_merge_is_reversible(tmp_path: Path):
    s = Store.load(tmp_path)
    body = r"A subshift $X\subseteq A^{\mathbb Z}$ is sofic."
    a = Node.from_dict(
        {"id": node_id(NodeKind.DEFINITION, body), "kind": "Definition",
         "statement_latex": body,
         "content_hash": content_hash("Definition", body)})
    s.nodes[a.id] = a
    s.save("seed")

    # same statement, cosmetically different -> different raw id, same hash
    body2 = r"A subshift $X \subset \mathbb{Z}$-... is sofic."
    b = Node.from_dict(
        {"id": "definition:other", "kind": "Definition",
         "statement_latex": body2,
         "content_hash": content_hash("Definition", body)})
    plan = plan_merge(s, [b], judge=ConservativeJudge())
    apply_plan(s, "arxiv:p2", [b], [], plan, run_id="m",
               reviews_dir=tmp_path / "reviews")
    assert len(s.merges) == 1
    assert s.nodes["definition:other"].is_tombstone
    assert s.resolve("definition:other") == a.id   # redirect works


# -- formalize ------------------------------------------------------------

def test_topo_and_next(tmp_path: Path):
    s = Store.load(tmp_path)
    d = Node(id="definition:d", kind="Definition", name="D")
    lem = Node(id="lemma:l", kind="Lemma", name="L")
    thm = Node(id="theorem:t", kind="Theorem", name="T")
    for n in (d, lem, thm):
        s.nodes[n.id] = n
    s.edges["e1"] = Edge(id="e1", type=EdgeType.USES_DEFINITION.value,
                         src="lemma:l", dst="definition:d")
    s.edges["e2"] = Edge(id="e2", type=EdgeType.DEPENDS_ON.value,
                         src="theorem:t", dst="lemma:l",
                         where_="in_statement")
    order = topo_order(s)
    assert order.index("definition:d") < order.index("lemma:l") < \
        order.index("theorem:t")
    nxt = next_targets(s, limit=5)
    # only the root (definition) is ready; lemma/thm blocked
    assert [t.id for t in nxt] == ["definition:d"]
    s.nodes["definition:d"].lean_status = "proved"
    assert [t.id for t in next_targets(s, limit=5)] == ["lemma:l"]


def test_stated_terminal_kinds_count_as_formalized(tmp_path: Path):
    # Definitions / Constructions / OpenProblems / Conjectures terminate
    # at ``stated`` (a Lean def of the object or the open-problem
    # statement is its formalization). Theorems / Lemmas don't — they
    # still need a proof.
    s = Store.load(tmp_path)
    s.nodes["definition:d"] = Node(id="definition:d", kind="Definition",
                                    lean_decl="X.d", lean_status="stated")
    s.nodes["construction:c"] = Node(id="construction:c", kind="Construction",
                                      lean_decl="X.c", lean_status="stated")
    s.nodes["openproblem:o"] = Node(id="openproblem:o", kind="OpenProblem",
                                     lean_decl="X.o", lean_status="stated")
    s.nodes["theorem:t"] = Node(id="theorem:t", kind="Theorem",
                                 lean_decl="X.t", lean_status="stated")
    nxt = {n.id for n in next_targets(s, limit=10)}
    assert {"definition:d", "construction:c", "openproblem:o"}.isdisjoint(nxt)
    assert "theorem:t" in nxt


# -- lints ----------------------------------------------------------------

def test_lints_detect_dangling_and_cycle(tmp_path: Path):
    s = Store.load(tmp_path)
    s.nodes["theorem:a"] = Node(id="theorem:a", kind="Theorem")
    s.nodes["theorem:b"] = Node(id="theorem:b", kind="Theorem")
    s.edges["bad"] = Edge(id="bad", type="depends_on", src="theorem:a",
                          dst="theorem:ghost", where_="in_statement")
    r = run_lints(s)
    assert any("dangling" in e for e in r.errors)

    s.edges["bad"].dst = "theorem:b"
    s.edges["cyc"] = Edge(id="cyc", type="depends_on", src="theorem:b",
                          dst="theorem:a", where_="in_statement")
    r2 = run_lints(s)
    assert any("cycle" in e for e in r2.errors)


# -- embed ----------------------------------------------------------------

def test_embed_deterministic_topk():
    e = HashingEmbedder(dim=64)
    v1 = e.embed("sofic shift entropy")
    assert v1 == e.embed("sofic shift entropy")
    corpus = {"a": e.embed("sofic shift entropy"),
              "b": e.embed("totally unrelated topic")}
    top = cosine_topk(e.embed("sofic shift entropy"), corpus, 1)
    assert top[0][0] == "a"


def test_sync_lean_parses_pairs_and_status(tmp_path: Path):
    from ontology.sync_lean import (
        default_status_for,
        module_path,
        parse_file,
        resolve_slug,
        sync,
    )

    lean_root = tmp_path / "lean"
    (lean_root / "deps").mkdir(parents=True)
    sample = (lean_root / "deps" / "Foo.lean")
    sample.write_text(
        "/-- doc 1 -/\n"
        "-- @ontology: my:def:a\n"
        "def myDef : Nat := 0\n\n"
        "/-- doc 2 -/\n"
        "-- @ontology: my:thm:b\n"
        "theorem myThm : True := by\n"
        "  -- TODO: sorry  (this comment must not trigger sorry-detection)\n"
        "  trivial\n\n"
        "-- @ontology: my:thm:c\n"
        "theorem withSorry : True := by sorry\n\n"
        "-- @ontology: my:thm:d [axiomatized]\n"
        "theorem overridden : True := trivial\n"
    )
    anns = parse_file(sample, file_rel="deps/Foo.lean")
    by_slug = {a.slug: a for a in anns}
    assert by_slug["my:def:a"].kw == "def" and by_slug["my:def:a"].lean_name == "myDef"
    assert by_slug["my:thm:b"].has_sorry is False                  # comment-only sorry
    assert by_slug["my:thm:c"].has_sorry is True                   # real sorry tactic
    assert by_slug["my:thm:d"].status_override == "axiomatized"

    assert default_status_for("def", False) == "stated"
    assert default_status_for("theorem", False) == "proved"
    assert default_status_for("theorem", True) == "sorry"
    assert default_status_for("axiom", False) == "axiomatized"
    assert module_path("papers/HM/HM.lean") == "papers.HM.HM"

    # resolve_slug: id wins, alias works, ambiguity returns None.
    s = Store.load(tmp_path)
    s.nodes["definition:x"] = Node(id="definition:x", kind="Definition",
                                    aliases=["my:def:a"])
    s.nodes["theorem:y"] = Node(id="theorem:y", kind="Theorem",
                                 aliases=["my:thm:b", "my:thm:c"])
    s.nodes["theorem:z"] = Node(id="theorem:z", kind="Theorem",
                                 aliases=["my:thm:c"])      # ambiguous with y
    s.nodes["theorem:d_only"] = Node(id="theorem:d_only", kind="Theorem",
                                      aliases=["my:thm:d"])
    assert resolve_slug(s, "my:def:a") == "definition:x"
    assert resolve_slug(s, "definition:x") == "definition:x"   # id wins
    assert resolve_slug(s, "my:thm:c") is None                 # ambiguous
    assert resolve_slug(s, "no-such") is None

    # end-to-end sync writes lean_decl + lean_status; overridden one wins.
    report = sync(s, lean_root)
    assert report.updated == 3          # def:a, thm:b, thm:d
    assert any("my:thm:c" in u for u in report.unresolved)       # ambiguous
    assert s.nodes["definition:x"].lean_decl == "deps.Foo.myDef"
    assert s.nodes["definition:x"].lean_status == "stated"
    assert s.nodes["theorem:d_only"].lean_status == "axiomatized"


def test_sync_lean_namespace_qualifies(tmp_path: Path):
    from ontology.sync_lean import parse_file, sync

    lean_root = tmp_path / "lean"
    (lean_root / "deps").mkdir(parents=True)
    sample = lean_root / "deps" / "NS.lean"
    sample.write_text(
        "namespace Outer\n"
        "namespace Inner\n"
        "-- @ontology: my:def:deep\n"
        "def deep : Nat := 0\n"
        "end Inner\n"
        "-- @ontology: my:def:mid\n"
        "def mid : Nat := 0\n"
        "end Outer\n"
        "-- @ontology: my:def:top\n"
        "def top : Nat := 0\n"
        "section S\n"           # sections do NOT contribute to namespace
        "-- @ontology: my:def:in-section\n"
        "def inSec : Nat := 0\n"
        "end S\n"
    )
    anns = {a.slug: a.lean_name for a in parse_file(sample, file_rel="deps/NS.lean")}
    assert anns["my:def:deep"] == "Outer.Inner.deep"
    assert anns["my:def:mid"] == "Outer.mid"
    assert anns["my:def:top"] == "top"
    assert anns["my:def:in-section"] == "inSec"

    s = Store.load(tmp_path)
    s.nodes["definition:deep"] = Node(id="definition:deep", kind="Definition",
                                       aliases=["my:def:deep"])
    s.nodes["definition:mid"] = Node(id="definition:mid", kind="Definition",
                                      aliases=["my:def:mid"])
    s.nodes["definition:top"] = Node(id="definition:top", kind="Definition",
                                      aliases=["my:def:top"])
    s.nodes["definition:insec"] = Node(id="definition:insec", kind="Definition",
                                        aliases=["my:def:in-section"])
    sync(s, lean_root)
    assert s.nodes["definition:deep"].lean_decl == "deps.NS.Outer.Inner.deep"
    assert s.nodes["definition:mid"].lean_decl == "deps.NS.Outer.mid"
    assert s.nodes["definition:top"].lean_decl == "deps.NS.top"
    assert s.nodes["definition:insec"].lean_decl == "deps.NS.inSec"


def test_load_subgraph_roundtrip(tmp_path: Path):
    sg = extract_paper("arxiv:rt", SAMPLE_TEX, "r")
    p = tmp_path / "subgraph.json"
    p.write_text(json.dumps(sg))
    pid, nodes, edges, cites = load_subgraph(p)
    assert pid == "arxiv:rt" and nodes and edges
