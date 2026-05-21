"""``onto`` — the ontology pipeline CLI (ONTOLOGY_PLAN §7).

Subcommands: status · harvest · acquire · extract · dedup · merge ·
build · export · next · lint · gate. Each mutating command writes a run
manifest under ``build/runs/`` (operational log; reproducibility proper
is the git-tracked snapshot manifest hash).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import glob
import json
import os
import sys
from collections import Counter
from pathlib import Path

from . import acquire as acquire_mod
from . import export as export_mod
from . import extract as extract_mod
from . import harvest as harvest_mod
from . import sync_lean as sync_lean_mod
from .dedup import ConservativeJudge, plan_merge
from .formalize import next_targets
from .lints import run_lints
from .merge import apply_plan, load_subgraph
from .schema import new_run_id
from .store import Store


def _root(args) -> Path:
    if args.root:
        return Path(args.root)
    return Path(__file__).resolve().parents[1]


def _now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


# -- gates -----------------------------------------------------------------

def _gate_path(root: Path, gate: str) -> Path:
    return root / "reviews" / f"{gate.replace(':', '_')}.signed"


def gate_signed(root: Path, gate: str, store: Store) -> bool:
    p = _gate_path(root, gate)
    if not p.exists():
        return False
    data = json.loads(p.read_text())
    # A later snapshot change re-opens the gate (README).
    return data.get("snapshot_hash") == store.snapshot_hash()


def cmd_gate(args, root: Path, store: Store) -> int:
    if args.action == "sign":
        p = _gate_path(root, args.gate)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(
            json.dumps(
                {
                    "gate": args.gate,
                    "reviewer": os.environ.get("USER", "unknown"),
                    "snapshot_hash": store.snapshot_hash(),
                    "ts": _now(),
                },
                indent=2,
            )
        )
        print(f"signed {args.gate} (snapshot {store.snapshot_hash()[:12]})")
        return 0
    # status
    for g in ("G1", "G3"):
        print(f"{g}: {'OPEN (signed)' if gate_signed(root, g, store) else 'closed'}")
    for sp in sorted((root / "reviews").glob("G2_*.signed")):
        print(f"{sp.stem}: signed")
    return 0


# -- run manifest ----------------------------------------------------------

def _write_run(root: Path, run_id: str, cmd: str, summary: dict) -> None:
    d = root / "build" / "runs"
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{run_id}.json").write_text(
        json.dumps(
            {"run_id": run_id, "cmd": cmd, "ts": _now(), "summary": summary},
            indent=2,
            sort_keys=True,
        )
    )


# -- commands --------------------------------------------------------------

def cmd_status(args, root: Path, store: Store) -> int:
    rel = Counter(p.relevance or 0 for p in store.papers.values())
    tiers = Counter(p.fidelity_tier for p in store.papers.values() if p.fidelity_tier)
    shards_done = sum(1 for s in store.shards.values() if s.status == "done")
    kinds = Counter(n.kind for n in store.nodes.values() if not n.is_tombstone)
    etypes = Counter(e.type for e in store.edges.values())
    print(f"root: {root}")
    print(f"snapshot: {store.snapshot_hash()[:12] or '(empty)'}  "
          f"build {'STALE' if store.is_build_stale() else 'fresh'}")
    print(f"papers: {len(store.papers)}  by relevance {dict(sorted(rel.items()))}")
    print(f"  fidelity {dict(tiers)}")
    print(f"shards: {shards_done}/{len(store.shards)} done")
    print(f"nodes: {sum(kinds.values())}  {dict(sorted(kinds.items()))}")
    print(f"edges: {len(store.edges)}  {dict(sorted(etypes.items()))}")
    print(f"merges logged: {len(store.merges)}")
    g3 = root / "reviews" / "G3_merge_queue.jsonl"
    if g3.exists():
        print(f"G3 queue: {sum(1 for _ in g3.open())} awaiting review")
    print(f"gates: G1={'signed' if gate_signed(root,'G1',store) else 'closed'} "
          f"G3={'signed' if gate_signed(root,'G3',store) else 'closed'}")
    return 0


def cmd_harvest(args, root: Path, store: Store) -> int:
    run_id = new_run_id()
    added = harvest_mod.build_shards(store, year_from=args.year_from)
    print(f"shard matrix: +{added} new (total {len(store.shards)})")
    summary = harvest_mod.run_harvest(
        store,
        max_shards=args.max_shards,
        delay=0.0 if args.no_delay else 3.0,
    )
    print(json.dumps(summary, indent=2))
    store.save(run_id)
    md, csv = harvest_mod.write_g1_artifacts(store, root / "reviews")
    _write_run(root, run_id, "harvest", summary)
    print(f"\nG1 artifacts: {md}\n             {csv}")
    print("review, then: onto gate sign G1")
    return 0


def _require_g1(args, root: Path, store: Store) -> bool:
    if args.only or args.force:
        if not (args.only):
            print("warning: --force bypasses gate G1", file=sys.stderr)
        return True
    if not gate_signed(root, "G1", store):
        print("gate G1 not signed (run `onto gate sign G1` after review, "
              "or pass --only <id> for the pilot path)", file=sys.stderr)
        return False
    return True


def cmd_acquire(args, root: Path, store: Store) -> int:
    if not _require_g1(args, root, store):
        return 2
    run_id = new_run_id()
    summary = acquire_mod.run_acquire(
        store, root / "corpus",
        min_relevance=args.min_relevance,
        only=args.only, force=args.force,
    )
    print(json.dumps(summary, indent=2))
    store.save(run_id)
    _write_run(root, run_id, "acquire", summary)
    return 0


def cmd_extract(args, root: Path, store: Store) -> int:
    if not _require_g1(args, root, store):
        return 2
    run_id = new_run_id()
    summary = extract_mod.run_extract(
        store, root / "corpus", only=args.only, run_id=run_id
    )
    print(json.dumps(summary, indent=2))
    if args.batch:
        ids = args.only or [
            p.id for p in store.papers.values() if p.fidelity_tier == "source"
        ]
        sample = ids[: args.sample]
        path = extract_mod.write_g2_sample(
            root / "corpus", root / "reviews", args.batch, sample
        )
        print(f"G2 sample: {path}\nreview, then: onto gate sign G2:{args.batch}")
    _write_run(root, run_id, "extract", summary)
    return 0


def _iter_subgraphs(root: Path):
    """Yield per-paper subgraph.json paths. Gold subgraphs
    (``gold/*.subgraph.json``) supersede the structural baseline in
    ``corpus/<id>/subgraph.json`` for the same paper (ONTOLOGY_PLAN
    §10.2: pilot is hand-curated into gold/)."""
    gold_papers: set[str] = set()
    for p in sorted(glob.glob(str(root / "gold" / "*.subgraph.json"))):
        try:
            gold_papers.add(json.loads(Path(p).read_text())["paper"])
            yield Path(p)
        except (OSError, ValueError, KeyError):
            continue
    for p in sorted(glob.glob(str(root / "corpus" / "*" / "subgraph.json"))):
        try:
            pid = json.loads(Path(p).read_text())["paper"]
        except (OSError, ValueError, KeyError):
            continue
        if pid not in gold_papers:
            yield Path(p)


def cmd_dedup(args, root: Path, store: Store) -> int:
    """Dry-run: preview the merge plan + (re)build the G3 queue. No
    snapshot mutation."""
    totals = Counter()
    for sgp in _iter_subgraphs(root):
        _pid, nodes, _edges, _c = load_subgraph(sgp)
        plan = plan_merge(store, nodes, judge=ConservativeJudge(),
                          tau_high=args.tau_high, tau_low=args.tau_low)
        totals["merge"] += plan.n_merge
        totals["new"] += plan.n_new
        totals["review"] += plan.n_review
    print(json.dumps(dict(totals), indent=2))
    print("preview only — `onto merge` applies (non-destructively)")
    return 0


def cmd_merge(args, root: Path, store: Store) -> int:
    run_id = new_run_id()
    agg = Counter()
    for sgp in _iter_subgraphs(root):
        pid, nodes, edges, _c = load_subgraph(sgp)
        plan = plan_merge(store, nodes, judge=ConservativeJudge(),
                          tau_high=args.tau_high, tau_low=args.tau_low)
        s = apply_plan(store, pid, nodes, edges, plan,
                       run_id=run_id, reviews_dir=root / "reviews")
        for k, v in s.items():
            agg[k] += v
    print(json.dumps(dict(agg), indent=2))
    store.save(run_id)
    _write_run(root, run_id, "merge", dict(agg))
    if agg["g3_queued"]:
        print(f"\n{agg['g3_queued']} ambiguous items added UNMERGED and "
              f"queued at reviews/G3_merge_queue.jsonl (resolve, then "
              f"`onto gate sign G3`)")
    return 0


def cmd_build(args, root: Path, store: Store) -> int:
    from .embed import VectorIndex

    db = store.build()
    idx = VectorIndex(store.build_dir)
    idx.build(
        {
            n.id: (n.statement_text or n.statement_latex)
            for n in store.nodes.values()
            if not n.is_tombstone
        }
    )
    print(f"built {db} ({len(store.nodes)} nodes, {len(store.edges)} edges)")
    print(f"embeddings: {len(idx.vectors)} vectors")
    return 0


def cmd_export(args, root: Path, store: Store) -> int:
    text = export_mod.export(store, args.fmt, concept=args.concept)
    if args.out:
        Path(args.out).write_text(text, encoding="utf-8")
        print(f"wrote {args.out}")
    else:
        print(text)
    return 0


def cmd_next(args, root: Path, store: Store) -> int:
    tgts = next_targets(store, target=args.target, limit=args.limit)
    if not tgts:
        print("no ready unformalized nodes (graph empty or all blocked)")
        return 0
    for t in tgts:
        print(f"- [{t.kind}] {t.name or t.id}")
        print(f"    id: {t.id}")
        if t.deps:
            print(f"    deps: {', '.join(t.deps)}")
        if t.statement_text:
            print(f"    {t.statement_text}")
    return 0


def cmd_sync_lean(args, root: Path, store: Store) -> int:
    lean_root = Path(args.lean_root) if args.lean_root else (root / ".." / "SymbolicDynamics")
    lean_root = lean_root.resolve()
    print(f"scanning {lean_root}")
    report = sync_lean_mod.sync(store, lean_root, log=print)
    for w in report.stale_lean_decl:
        print(f"WARN  {w}")
    for u in report.unresolved:
        print(f"WARN  unresolved: {u}")
    for nd in report.no_decl:
        print(f"WARN  {nd}")
    print(
        f"\n{report.files_scanned} files · {report.annotations} annotations · "
        f"{report.updated} updated · {report.unchanged} unchanged · "
        f"{len(report.unresolved)} unresolved · {len(report.no_decl)} dangling"
    )
    if not args.dry_run and report.updated:
        run_id = new_run_id()
        store.save(run_id)
        _write_run(root, run_id, "sync-lean",
                   {"updated": report.updated,
                    "unresolved": len(report.unresolved)})
    return 0 if report.ok else 1


def cmd_lint(args, root: Path, store: Store) -> int:
    r = run_lints(store)
    for w in r.warnings:
        print(f"WARN  {w}")
    for e in r.errors:
        print(f"ERROR {e}")
    print(f"\n{len(r.errors)} errors, {len(r.warnings)} warnings")
    return 0 if r.ok else 1


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="onto", description=__doc__)
    p.add_argument("--root", help="ontology project dir (default: package parent)")
    sub = p.add_subparsers(dest="cmd", required=True)

    sub.add_parser("status").set_defaults(fn=cmd_status)

    h = sub.add_parser("harvest")
    h.add_argument("--year-from", type=int, default=None)
    h.add_argument("--max-shards", type=int, default=None)
    h.add_argument("--no-delay", action="store_true")
    h.set_defaults(fn=cmd_harvest)

    a = sub.add_parser("acquire")
    a.add_argument("--only", nargs="*", default=None, help="explicit paper ids (pilot)")
    a.add_argument("--min-relevance", type=int, default=2)
    a.add_argument("--force", action="store_true")
    a.set_defaults(fn=cmd_acquire)

    x = sub.add_parser("extract")
    x.add_argument("--only", nargs="*", default=None)
    x.add_argument("--batch", default=None, help="name -> write a G2 sample")
    x.add_argument("--sample", type=int, default=3)
    x.add_argument("--force", action="store_true")
    x.set_defaults(fn=cmd_extract)

    for name, fn in (("dedup", cmd_dedup), ("merge", cmd_merge)):
        m = sub.add_parser(name)
        m.add_argument("--tau-high", type=float, default=0.92)
        m.add_argument("--tau-low", type=float, default=0.55)
        m.set_defaults(fn=fn)

    sub.add_parser("build").set_defaults(fn=cmd_build)

    e = sub.add_parser("export")
    e.add_argument("fmt", choices=["graphml", "cypher", "mermaid", "jsonl"])
    e.add_argument("--concept", default=None)
    e.add_argument("--out", default=None)
    e.set_defaults(fn=cmd_export)

    n = sub.add_parser("next")
    n.add_argument("--target", nargs="*", default=None)
    n.add_argument("--limit", type=int, default=5)
    n.set_defaults(fn=cmd_next)

    sub.add_parser("lint").set_defaults(fn=cmd_lint)

    sl = sub.add_parser("sync-lean")
    sl.add_argument("--lean-root", default=None,
                    help="Lean project root (default ../SymbolicDynamics)")
    sl.add_argument("--dry-run", action="store_true")
    sl.set_defaults(fn=cmd_sync_lean)

    g = sub.add_parser("gate")
    g.add_argument("action", choices=["sign", "status"])
    g.add_argument("gate", nargs="?", default="", help="G1 | G2:<batch> | G3")
    g.set_defaults(fn=cmd_gate)
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    root = _root(args)
    store = Store.load(root)
    return args.fn(args, root, store)


if __name__ == "__main__":
    raise SystemExit(main())
