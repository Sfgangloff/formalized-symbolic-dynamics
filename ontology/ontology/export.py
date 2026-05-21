"""Graph exporters (ONTOLOGY_PLAN §7: GraphML / Cypher / mermaid / JSONL).

GraphML and Cypher are full-graph dumps for external graph tools; mermaid
is the per-concept equivalence-map view that ROADMAP §4.4 wants embedded
at the top of each dictionary page.
"""

from __future__ import annotations

import json
import re
from xml.sax.saxutils import escape

from .schema import EdgeType
from .store import Store


def _live_nodes(store: Store):
    return [n for n in store.nodes.values() if not n.is_tombstone]


def to_graphml(store: Store) -> str:
    out = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<graphml xmlns="http://graphml.graphdrawing.org/xmlns">',
        '<key id="kind" for="node" attr.name="kind" attr.type="string"/>',
        '<key id="name" for="node" attr.name="name" attr.type="string"/>',
        '<key id="etype" for="edge" attr.name="type" attr.type="string"/>',
        '<graph edgedefault="directed">',
    ]
    for n in _live_nodes(store):
        out.append(
            f'<node id="{escape(n.id)}">'
            f'<data key="kind">{escape(n.kind)}</data>'
            f'<data key="name">{escape(n.name)}</data></node>'
        )
    for e in store.edges.values():
        s, d = store.resolve(e.src), store.resolve(e.dst)
        out.append(
            f'<edge source="{escape(s)}" target="{escape(d)}">'
            f'<data key="etype">{escape(e.type)}</data></edge>'
        )
    out += ["</graph>", "</graphml>"]
    return "\n".join(out)


def to_cypher(store: Store) -> str:
    lines = []
    for n in _live_nodes(store):
        nm = n.name.replace("'", "\\'")
        lines.append(
            f"MERGE (n:`{n.kind}` {{id:'{n.id}'}}) SET n.name='{nm}';"
        )
    for e in store.edges.values():
        s, d = store.resolve(e.src), store.resolve(e.dst)
        lines.append(
            f"MATCH (a {{id:'{s}'}}),(b {{id:'{d}'}}) "
            f"MERGE (a)-[:`{e.type}`]->(b);"
        )
    return "\n".join(lines)


_SAFE = re.compile(r"[^A-Za-z0-9]")


def to_mermaid(store: Store, concept: str | None = None) -> str:
    """Per-concept equivalence map (§4.4). With ``concept`` set, restrict
    to definitions ``instance_of`` it plus their ``equivalent_to`` edges."""
    keep: set[str] | None = None
    if concept:
        keep = set()
        for e in store.edges.values():
            if e.type == EdgeType.INSTANCE_OF.value and store.resolve(e.dst) == concept:
                keep.add(store.resolve(e.src))
        keep.add(concept)

    def sid(x: str) -> str:
        return "n_" + _SAFE.sub("_", x)

    lines = ["graph TD"]
    for n in _live_nodes(store):
        if keep is not None and n.id not in keep:
            continue
        disp = n.name or (n.statement_text[:48] + "…" if n.statement_text else n.id)
        label = f"{n.kind}: {disp}".replace('"', "'").replace("[", "(").replace("]", ")")
        lines.append(f'  {sid(n.id)}["{label}"]')
    for e in store.edges.values():
        s, d = store.resolve(e.src), store.resolve(e.dst)
        if keep is not None and (s not in keep or d not in keep):
            continue
        if keep is not None and e.type != EdgeType.EQUIVALENT_TO.value:
            continue
        lines.append(f"  {sid(s)} -->|{e.type}| {sid(d)}")
    return "\n".join(lines)


def to_jsonl(store: Store) -> str:
    rows = (
        [{"_": "node", **n.to_dict()} for n in _live_nodes(store)]
        + [{"_": "edge", **e.to_dict()} for e in store.edges.values()]
    )
    return "".join(json.dumps(r, sort_keys=True) + "\n" for r in rows)


def export(store: Store, fmt: str, concept: str | None = None) -> str:
    fmt = fmt.lower()
    if fmt == "graphml":
        return to_graphml(store)
    if fmt == "cypher":
        return to_cypher(store)
    if fmt == "mermaid":
        return to_mermaid(store, concept)
    if fmt == "jsonl":
        return to_jsonl(store)
    raise ValueError(f"unknown export format {fmt!r} (graphml|cypher|mermaid|jsonl)")
