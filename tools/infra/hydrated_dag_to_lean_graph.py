#!/usr/bin/env python3
"""Project the hydrated SCC DAG into lean-graph's simple JSON schema.

`patrik-cihal/lean-graph` expects a list of objects:

    {
      "name": "...",
      "constCategory": "Theorem|Definition|Axiom|Other",
      "constType": "...",
      "references": ["..."]
    }

The hydrated DAG artifact is richer and usually much larger.  This adapter
emits a bounded, human-viewable slice:

* an apex causal diamond, if `--apex` is supplied;
* otherwise a module/prefix slice, if `--prefix` is supplied;
* otherwise the first `--max-nodes` components.

Orientation is preserved as `component -> dependencies` in `references`, which
is exactly the convention lean-graph uses for its extracted declaration JSON.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path
from typing import Any


def load_structure(path: Path) -> tuple[dict[str, Any], dict[str, dict[str, Any]], dict[str, str]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    components = payload.get("components")
    if not isinstance(components, list):
        raise SystemExit(f"{path} does not contain a top-level components list")

    by_id: dict[str, dict[str, Any]] = {}
    name_to_id: dict[str, str] = {}
    for c in components:
        if not isinstance(c, dict):
            continue
        cid = c.get("componentId")
        rep = c.get("representative")
        if not isinstance(cid, str) or not isinstance(rep, str):
            continue
        by_id[cid] = c
        name_to_id[rep] = cid
        for member in c.get("members") or []:
            if isinstance(member, str):
                name_to_id[member] = cid
    return payload, by_id, name_to_id


def component_name(c: dict[str, Any], *, id_fallback: str) -> str:
    rep = c.get("representative")
    return rep if isinstance(rep, str) and rep else id_fallback


def bfs_ids(
    by_id: dict[str, dict[str, Any]],
    *,
    seed: str,
    field: str,
    depth: int,
    limit: int,
) -> set[str]:
    if depth <= 0 or seed not in by_id:
        return set()
    seen: set[str] = {seed}
    out: set[str] = set()
    q: deque[tuple[str, int]] = deque([(seed, 0)])
    while q and len(out) < limit:
        cid, d = q.popleft()
        if d >= depth:
            continue
        for nxt in by_id[cid].get(field) or []:
            if not isinstance(nxt, str) or nxt in seen or nxt not in by_id:
                continue
            seen.add(nxt)
            out.add(nxt)
            if len(out) >= limit:
                break
            q.append((nxt, d + 1))
    return out


def select_ids(args: argparse.Namespace, by_id: dict[str, dict[str, Any]], name_to_id: dict[str, str]) -> set[str]:
    if args.apex:
        seed = name_to_id.get(args.apex)
        if seed is None:
            raise SystemExit(f"apex declaration/component not found in hydrated DAG: {args.apex}")
        ids = {seed}
        ids |= bfs_ids(
            by_id,
            seed=seed,
            field="dependencyComponentIds",
            depth=args.backward_depth,
            limit=args.max_nodes,
        )
        remaining = max(args.max_nodes - len(ids), 0)
        ids |= bfs_ids(
            by_id,
            seed=seed,
            field="reverseDependentComponentIds",
            depth=args.forward_depth,
            limit=remaining,
        )
        return set(list(ids)[: args.max_nodes])

    rows = list(by_id.items())
    rows.sort(key=lambda item: int(item[1].get("componentIndex") or 0))
    if args.prefix:
        rows = [
            (cid, c)
            for cid, c in rows
            if component_name(c, id_fallback=cid).startswith(args.prefix)
            or any(isinstance(m, str) and m.startswith(args.prefix) for m in c.get("members") or [])
        ]
    return {cid for cid, _ in rows[: args.max_nodes]}


def category_for(c: dict[str, Any]) -> str:
    # lean-graph's default UI hides `Other`, so keep components visible by using
    # the existing display categories as structural tags.
    if c.get("isRoot"):
        return "Definition"
    if c.get("isCapstone"):
        return "Theorem"
    if int(c.get("strictDominatorCount") or 0) > 0:
        return "Axiom"
    return "Definition"


def const_type_for(c: dict[str, Any], *, cid: str) -> str:
    fields = [
        f"componentId={cid}",
        f"componentIndex={c.get('componentIndex')}",
        f"size={c.get('size')}",
        f"depthMin={c.get('depthMin')}",
        f"depthMax={c.get('depthMax')}",
        f"isRoot={c.get('isRoot')}",
        f"isCapstone={c.get('isCapstone')}",
        f"strictDominatorCount={c.get('strictDominatorCount')}",
    ]
    return "Hydrated SCC component; " + "; ".join(fields)


def to_lean_graph_json(by_id: dict[str, dict[str, Any]], ids: set[str]) -> list[dict[str, Any]]:
    names = {cid: component_name(by_id[cid], id_fallback=cid) for cid in ids if cid in by_id}
    rows: list[dict[str, Any]] = []
    for cid in sorted(ids, key=lambda x: int(by_id[x].get("componentIndex") or 0)):
        c = by_id[cid]
        refs: list[str] = []
        for dep in c.get("dependencyComponentIds") or []:
            if isinstance(dep, str) and dep in names:
                refs.append(names[dep])
        rows.append(
            {
                "name": names[cid],
                "constCategory": category_for(c),
                "constType": const_type_for(c, cid=cid),
                "references": sorted(set(refs)),
            }
        )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--structure", type=Path, default=Path("artifacts/dag/structural-topology.json"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--apex", help="Declaration/member/representative to use as causal-diamond apex")
    parser.add_argument("--prefix", help="Fallback prefix slice when no apex is supplied")
    parser.add_argument("--backward-depth", type=int, default=2)
    parser.add_argument("--forward-depth", type=int, default=1)
    parser.add_argument("--max-nodes", type=int, default=300)
    args = parser.parse_args()

    _payload, by_id, name_to_id = load_structure(args.structure)
    ids = select_ids(args, by_id, name_to_id)
    rows = to_lean_graph_json(by_id, ids)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(rows, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"wrote {len(rows)} lean-graph nodes to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
