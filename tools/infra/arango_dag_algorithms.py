#!/usr/bin/env python3
"""Run DAG graph algorithms over the live Arango topology overlay.

This is a derived overlay engine. It does not rewrite raw graph collections and
does not replace the Lean-owned DAG exporters. The default input is the
lossless raw-DAG SCC overlay:

  topology_overlay         SCC/component vertices
  topology_overlay_edges   member_of_scc and scc_quotient edges

The output, when --write is provided, goes to separate arango_dag_* collections.
Those rows are navigation/analytics overlays and must remain witness-descendable
through the original scc_quotient edges.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import quote

from arango_raw_infotree_ingest import (
    ArangoTarget,
    CollectionSpec,
    collection_count,
    create_collection,
    db_url,
    drop_collection,
    ensure_database,
    list_collections,
    request_json,
)


SCHEMA = "info_geometry.arango_dag_algorithms.v1"
DEFAULT_GRAPH_NAME = "arango_dag"
REP_LAYERS = [
    "L0_Count",
    "L1_Projective",
    "L2_Operator",
    "L3_Krein",
    "L4_ModularTransport",
    "L5_ThermodynamicClosure",
]

PROCESS_DEFECT_SEVERITY = {
    "illicitBoundaryCrossing": 5,
    "regressiveFlow": 5,
    "boundaryBypass": 4,
    "remoteAttachment": 3,
    "failedLocalFactorization": 3,
    "mixedPolarity": 2,
    "unclearPolarity": 2,
    "typeOnlySupport": 1,
    "unresolvedComparison": 1,
}


@dataclass(frozen=True)
class QuotientGraph:
    nodes: list[dict[str, Any]]
    node_index: dict[str, int]
    ids: list[str]
    keys: list[str]
    forward: list[list[int]]
    preds: list[list[int]]
    edge_rows: list[dict[str, Any]]
    edge_multiplicity: dict[tuple[int, int], int]
    edge_witness_counts: dict[tuple[int, int], int]
    layer_counts: list[dict[str, int]]
    dominant_layer: list[str | None]
    dominant_depth: list[int | None]


def layer_depth(layer: str | None) -> int | None:
    if not layer:
        return None
    for i, name in enumerate(REP_LAYERS):
        if layer == name:
            return i
    return None


def flow_polarity(src_depth: int | None, dst_depth: int | None) -> str:
    if src_depth is None or dst_depth is None:
        return "unlabeled"
    if src_depth == dst_depth:
        return "same_layer"
    if src_depth < dst_depth:
        return "ascending"
    if src_depth == dst_depth + 1:
        return "descending_adjacent"
    return "regressive"


def process_dependency_role(src_depth: int | None, dst_depth: int | None, edge_kind: str | None) -> str:
    if src_depth is None or dst_depth is None:
        return "unknown"
    edge_use_has_value = edge_kind != "type"
    if src_depth < dst_depth:
        return "remoteSupport"
    if dst_depth + 1 < src_depth:
        return "remoteSupport"
    if dst_depth + 1 == src_depth:
        return "transportArg" if edge_use_has_value else "requiredArg"
    return "head" if edge_use_has_value else "witness"


def process_boundary_class(src_depth: int | None, dst_depth: int | None, role: str, src_capstone: bool) -> str:
    if src_capstone:
        return "capstone"
    if role == "transportArg":
        return "bridge"
    if src_depth is None or dst_depth is None:
        return "unclear"
    if src_depth == dst_depth:
        return "internal"
    if src_depth == dst_depth + 1:
        return "localInterface"
    if dst_depth > src_depth or dst_depth + 1 < src_depth:
        return "mixed"
    return "unclear"


def process_locality_class(src_depth: int | None, dst_depth: int | None) -> str:
    if src_depth is None or dst_depth is None:
        return "mixed"
    if dst_depth > src_depth:
        return "mixed"
    if dst_depth + 1 < src_depth:
        return "remote"
    if dst_depth + 1 == src_depth:
        return "adjacent"
    return "local"


def process_defect_tags(
    *,
    src_depth: int | None,
    dst_depth: int | None,
    src_capstone: bool,
    role: str,
    boundary: str,
    polarity: str,
    edge_kind: str | None,
) -> list[str]:
    tags: list[str] = []
    if role == "remoteSupport":
        tags.append("remoteAttachment")
    if src_depth is not None and dst_depth is not None:
        if dst_depth > src_depth:
            tags.append("regressiveFlow")
        if dst_depth + 1 < src_depth and not src_capstone:
            tags.extend(["boundaryBypass", "failedLocalFactorization"])
    if boundary == "mixed":
        tags.append("illicitBoundaryCrossing")
    if polarity == "mixed":
        tags.append("mixedPolarity")
    if polarity == "unlabeled" and role == "remoteSupport":
        tags.append("unclearPolarity")
    if edge_kind == "type" and role in {"remoteSupport", "witness"}:
        tags.append("typeOnlySupport")
    out: list[str] = []
    for tag in tags:
        if tag not in out:
            out.append(tag)
    return out


def defect_cost(tags: list[str]) -> int:
    return sum(PROCESS_DEFECT_SEVERITY.get(tag, 1) for tag in tags)


def layer_histogram_to_array(counts: dict[str, int]) -> list[dict[str, Any]]:
    return [{"layer": k, "count": v, "depth": layer_depth(k)} for k, v in sorted(counts.items())]


def run_aql(target: ArangoTarget, query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
    payload = {
        "query": query,
        "bindVars": bind_vars or {},
        "batchSize": 10000,
        "options": {"fullCount": False},
    }
    out = request_json(
        "POST",
        db_url(target, "/_api/cursor"),
        username=target.username,
        password=target.password,
        payload=payload,
    )
    if not isinstance(out, dict):
        raise RuntimeError(f"Unexpected AQL response: {out!r}")
    result = list(out.get("result", []))
    cursor_id = out.get("id")
    while out.get("hasMore"):
        out = request_json(
            "PUT",
            db_url(target, f"/_api/cursor/{quote(str(cursor_id))}"),
            username=target.username,
            password=target.password,
        )
        if not isinstance(out, dict):
            raise RuntimeError(f"Unexpected cursor response: {out!r}")
        result.extend(out.get("result", []))
        cursor_id = out.get("id", cursor_id)
    return result


def load_quotient_graph(
    target: ArangoTarget,
    *,
    overlay_nodes: str,
    overlay_edges: str,
    edge_kind: str | None,
) -> QuotientGraph:
    nodes = run_aql(
        target,
        """
        FOR n IN @@nodes
          SORT n.scc_id ASC
          RETURN n
        """,
        {"@nodes": overlay_nodes},
    )
    node_index = {str(row["_id"]): i for i, row in enumerate(nodes)}
    ids = [str(row["_id"]) for row in nodes]
    keys = [str(row["_key"]) for row in nodes]

    layer_rows = run_aql(
        target,
        """
        FOR e IN @@edges
          FILTER e.role == "member_of_scc"
          LET raw = DOCUMENT(e._from)
          FILTER raw != null && raw.rep_layer != null
          COLLECT scc = e._to, layer = raw.rep_layer INTO groupRows
          RETURN {scc: scc, layer: layer, count: LENGTH(groupRows)}
        """,
        {"@edges": overlay_edges},
    )
    layer_counts_by_id: dict[str, dict[str, int]] = {}
    for row in layer_rows:
        scc = str(row.get("scc"))
        layer = str(row.get("layer"))
        layer_counts_by_id.setdefault(scc, {})[layer] = int(row.get("count") or 0)

    layer_counts: list[dict[str, int]] = []
    dominant_layer: list[str | None] = []
    dominant_depth: list[int | None] = []
    for node_id in ids:
        counts = layer_counts_by_id.get(node_id, {})
        layer_counts.append(counts)
        if counts:
            dom = sorted(counts.items(), key=lambda kv: (kv[1], -(layer_depth(kv[0]) or 99), kv[0]), reverse=True)[0][0]
            dominant_layer.append(dom)
            dominant_depth.append(layer_depth(dom))
        else:
            dominant_layer.append(None)
            dominant_depth.append(None)

    bind: dict[str, Any] = {"@edges": overlay_edges}
    kind_filter = ""
    if edge_kind:
        bind["kind"] = edge_kind
        kind_filter = "&& e.kind == @kind"
    edge_rows = run_aql(
        target,
        f"""
        FOR e IN @@edges
          FILTER e.role == "scc_quotient" {kind_filter}
          RETURN {{
            _key: e._key,
            _id: e._id,
            _from: e._from,
            _to: e._to,
            kind: e.kind,
            multiplicity: e.multiplicity,
            witness_count: LENGTH(e.witness_raw_edge_keys || []),
            witness_overflow_count: e.witness_overflow_count || 0
          }}
        """,
        bind,
    )

    forward_sets: list[set[int]] = [set() for _ in nodes]
    pred_sets: list[set[int]] = [set() for _ in nodes]
    edge_multiplicity: dict[tuple[int, int], int] = {}
    edge_witness_counts: dict[tuple[int, int], int] = {}

    for edge in edge_rows:
        src = node_index.get(str(edge.get("_from")))
        dst = node_index.get(str(edge.get("_to")))
        if src is None or dst is None or src == dst:
            continue
        forward_sets[src].add(dst)
        pred_sets[dst].add(src)
        key = (src, dst)
        edge_multiplicity[key] = edge_multiplicity.get(key, 0) + int(edge.get("multiplicity") or 1)
        edge_witness_counts[key] = (
            edge_witness_counts.get(key, 0)
            + int(edge.get("witness_count") or 0)
            + int(edge.get("witness_overflow_count") or 0)
        )

    forward = [sorted(xs) for xs in forward_sets]
    preds = [sorted(xs) for xs in pred_sets]
    return QuotientGraph(
        nodes=nodes,
        node_index=node_index,
        ids=ids,
        keys=keys,
        forward=forward,
        preds=preds,
        edge_rows=edge_rows,
        edge_multiplicity=edge_multiplicity,
        edge_witness_counts=edge_witness_counts,
        layer_counts=layer_counts,
        dominant_layer=dominant_layer,
        dominant_depth=dominant_depth,
    )


def topo(forward: list[list[int]], preds: list[list[int]]) -> tuple[list[int], list[int]]:
    indeg = [len(ps) for ps in preds]
    queue = deque(i for i, d in enumerate(indeg) if d == 0)
    out: list[int] = []
    while queue:
        u = queue.popleft()
        out.append(u)
        for v in forward[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                queue.append(v)
    cyclic_residue = [i for i, d in enumerate(indeg) if d != 0]
    return out, cyclic_residue


def bfs_dist(adj: list[list[int]], starts: Iterable[int]) -> list[int | None]:
    dist: list[int | None] = [None] * len(adj)
    queue: deque[int] = deque()
    for s in starts:
        if dist[s] is None:
            dist[s] = 0
            queue.append(s)
    while queue:
        u = queue.popleft()
        du = dist[u]
        if du is None:
            continue
        for v in adj[u]:
            if dist[v] is None:
                dist[v] = du + 1
                queue.append(v)
    return dist


def dag_longest_depth_with_pred(
    adj: list[list[int]],
    order: list[int],
    starts: Iterable[int],
) -> tuple[list[int | None], list[int | None]]:
    depth: list[int | None] = [None] * len(adj)
    pred: list[int | None] = [None] * len(adj)
    for s in starts:
        depth[s] = 0
    for u in order:
        du = depth[u]
        if du is None:
            continue
        for v in adj[u]:
            old = depth[v]
            cand = du + 1
            if old is None or old < cand:
                depth[v] = cand
                pred[v] = u
    return depth, pred


def dag_longest_depth(adj: list[list[int]], order: list[int], starts: Iterable[int]) -> list[int | None]:
    return dag_longest_depth_with_pred(adj, order, starts)[0]


def path_counts(adj: list[list[int]], order: list[int], src: int) -> list[int]:
    counts = [0] * len(adj)
    counts[src] = 1
    for u in order:
        cu = counts[u]
        if not cu:
            continue
        for v in adj[u]:
            counts[v] += cu
    return counts


def dominator_counts(preds: list[list[int]], order: list[int]) -> list[int]:
    n = len(preds)
    all_bits = (1 << n) - 1
    dom = [all_bits] * n
    for u in order:
        ps = preds[u]
        if not ps:
            base = 0
        else:
            base = dom[ps[0]]
            for p in ps[1:]:
                base &= dom[p]
        dom[u] = base | (1 << u)
    return [mask.bit_count() - 1 for mask in dom]


def dominator_masks(preds: list[list[int]], order: list[int]) -> list[int]:
    n = len(preds)
    all_bits = (1 << n) - 1
    dom = [all_bits] * n
    for u in order:
        ps = preds[u]
        if not ps:
            base = 0
        else:
            base = dom[ps[0]]
            for p in ps[1:]:
                base &= dom[p]
        dom[u] = base | (1 << u)
    return dom


def stable_hash(obj: Any) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.blake2b(payload.encode("utf-8"), digest_size=16).hexdigest()


def choose_seed(graph: QuotientGraph, representative: str | None, scc_id: int | None) -> int | None:
    if scc_id is not None:
        for i, row in enumerate(graph.nodes):
            if row.get("scc_id") == scc_id:
                return i
    if representative:
        rep_l = representative.lower()
        best: tuple[int, int] | None = None
        for i, row in enumerate(graph.nodes):
            hay = " ".join(
                [
                    str(row.get("representative") or ""),
                    " ".join(map(str, row.get("sample_members") or [])),
                    str(row.get("component_id") or ""),
                ]
            ).lower()
            if representative == row.get("representative"):
                return i
            if rep_l in hay:
                score = len(hay)
                if best is None or score < best[0]:
                    best = (score, i)
        if best is not None:
            return best[1]
    return None


def component_docs(
    graph: QuotientGraph,
    *,
    order: list[int],
    roots: list[int],
    capstones: list[int],
    depth_min: list[int | None],
    depth_max: list[int | None],
    dom_counts: list[int] | None,
    seed: int | None,
    seed_down_dist: list[int | None] | None,
    seed_up_dist: list[int | None] | None,
    seed_down_paths: list[int] | None,
    seed_up_paths: list[int] | None,
    run_id: str,
) -> list[dict[str, Any]]:
    topo_rank = {u: i for i, u in enumerate(order)}
    root_set = set(roots)
    capstone_set = set(capstones)
    docs = []
    for i, row in enumerate(graph.nodes):
        docs.append(
            {
                "_key": graph.keys[i],
                "schema": SCHEMA,
                "run_id": run_id,
                "source_id": graph.ids[i],
                "source_key": graph.keys[i],
                "scc_id": row.get("scc_id"),
                "component_id": row.get("component_id"),
                "representative": row.get("representative"),
                "member_count": row.get("member_count"),
                "sample_members": row.get("sample_members"),
                "rep_layer_counts": layer_histogram_to_array(graph.layer_counts[i]),
                "rep_layer_count_map": graph.layer_counts[i],
                "dominant_rep_layer": graph.dominant_layer[i],
                "dominant_rep_depth": graph.dominant_depth[i],
                "in_degree": len(graph.preds[i]),
                "out_degree": len(graph.forward[i]),
                "is_dependency_root": i in roots,
                "is_capstone": i in capstone_set,
                "topo_rank": topo_rank.get(i),
                "depth_min_from_dependency_roots": depth_min[i],
                "depth_max_from_dependency_roots": depth_max[i],
                "depth_spread_from_dependency_roots": (
                    None if depth_min[i] is None or depth_max[i] is None else depth_max[i] - depth_min[i]
                ),
                "strict_dominator_count": None if dom_counts is None else dom_counts[i],
                "seed_down_distance": None if seed_down_dist is None else seed_down_dist[i],
                "seed_up_distance": None if seed_up_dist is None else seed_up_dist[i],
                "seed_down_path_count": None if seed_down_paths is None else seed_down_paths[i],
                "seed_up_path_count": None if seed_up_paths is None else seed_up_paths[i],
                "labels": ["overlay:arango_dag", "truth_status:derived_navigation"],
            }
        )
    return docs


def component_edge_docs(graph: QuotientGraph, *, run_id: str) -> list[dict[str, Any]]:
    docs = []
    for (src, dst), multiplicity in sorted(graph.edge_multiplicity.items()):
        src_depth = graph.dominant_depth[src]
        dst_depth = graph.dominant_depth[dst]
        polarity = flow_polarity(src_depth, dst_depth)
        docs.append(
            {
                "_key": f"{graph.keys[src]}__to__{graph.keys[dst]}",
                "_from": f"arango_dag_components/{graph.keys[src]}",
                "_to": f"arango_dag_components/{graph.keys[dst]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "source_from": graph.ids[src],
                "source_to": graph.ids[dst],
                "source_layer": graph.dominant_layer[src],
                "target_layer": graph.dominant_layer[dst],
                "source_depth": src_depth,
                "target_depth": dst_depth,
                "layer_flow": (
                    None
                    if graph.dominant_layer[src] is None or graph.dominant_layer[dst] is None
                    else f"{graph.dominant_layer[src]}->{graph.dominant_layer[dst]}"
                ),
                "flow_polarity": polarity,
                "regressive": polarity == "regressive",
                "multiplicity": multiplicity,
                "witness_count": graph.edge_witness_counts.get((src, dst), 0),
                "role": "arango_dag_quotient_edge",
                "labels": ["overlay:arango_dag", "descent:witness_backed"],
            }
        )
    return docs


def layer_docs(
    graph: QuotientGraph,
    *,
    depth_min: list[int | None],
    run_id: str,
    node_preview_limit: int,
) -> list[dict[str, Any]]:
    by_depth: dict[int, list[int]] = {}
    for i, depth in enumerate(depth_min):
        if depth is not None:
            by_depth.setdefault(depth, []).append(i)
    docs = []
    for depth, indices in sorted(by_depth.items()):
        reps = [str(graph.nodes[i].get("representative") or graph.keys[i]) for i in indices[:node_preview_limit]]
        docs.append(
            {
                "_key": f"layer_{depth}",
                "schema": SCHEMA,
                "run_id": run_id,
                "depth": depth,
                "size": len(indices),
                "node_preview_limit": node_preview_limit,
                "representative_preview": reps,
                "labels": ["overlay:arango_dag", "role:topological_layer"],
            }
        )
    return docs


def deepest_chain_docs(
    graph: QuotientGraph,
    *,
    depth_max: list[int | None],
    max_pred: list[int | None],
    run_id: str,
    limit: int,
) -> list[dict[str, Any]]:
    deepest = max((d for d in depth_max if d is not None), default=0)
    endpoints = [i for i, d in enumerate(depth_max) if d == deepest]
    docs = []
    for chain_idx, endpoint in enumerate(endpoints[:limit]):
        chain = []
        seen = set()
        cur: int | None = endpoint
        while cur is not None and cur not in seen:
            seen.add(cur)
            chain.append(cur)
            cur = max_pred[cur]
        chain = list(reversed(chain))
        docs.append(
            {
                "_key": f"chain_{chain_idx}_{graph.keys[endpoint]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "depth": max(len(chain) - 1, 0),
                "endpoint": graph.ids[endpoint],
                "endpoint_representative": graph.nodes[endpoint].get("representative"),
                "component_keys": [graph.keys[i] for i in chain],
                "representatives": [graph.nodes[i].get("representative") for i in chain],
                "labels": ["overlay:arango_dag", "role:deepest_root_chain"],
            }
        )
    return docs


def bounded_root_contribs(
    graph: QuotientGraph,
    *,
    roots: list[int],
    order_from_roots: list[int],
    dst: int,
    limit: int,
) -> list[dict[str, Any]]:
    # Bounded version of Analysis.rootContributionCounts. Exact path counts are
    # computed only for the selected top roots to avoid the 6486 x 7649
    # all-pairs explosion on the current graph.
    if limit <= 0:
        return []
    ranked_roots = sorted(roots, key=lambda r: len(graph.preds[r]) + len(graph.forward[r]), reverse=True)
    out = []
    for root in ranked_roots[:limit]:
        counts = path_counts(graph.preds, order_from_roots, root)
        c = counts[dst]
        if c:
            out.append(
                {
                    "component_key": graph.keys[root],
                    "representative": graph.nodes[root].get("representative"),
                    "paths": c,
                }
            )
    return sorted(out, key=lambda row: int(row["paths"]), reverse=True)


def capstone_docs(
    graph: QuotientGraph,
    *,
    capstones: list[int],
    roots: list[int],
    depth_min: list[int | None],
    depth_max: list[int | None],
    run_id: str,
    capstone_limit: int,
    root_contrib_limit: int,
    order_from_roots: list[int],
) -> list[dict[str, Any]]:
    ranked = sorted(
        capstones,
        key=lambda i: (
            -1 if depth_max[i] is None else depth_max[i],
            len(graph.preds[i]),
            graph.nodes[i].get("representative") or "",
        ),
        reverse=True,
    )
    docs = []
    for idx, comp in enumerate(ranked[:capstone_limit]):
        mn = depth_min[comp]
        mx = depth_max[comp]
        docs.append(
            {
                "_key": f"capstone_{idx}_{graph.keys[comp]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "component_key": graph.keys[comp],
                "source_id": graph.ids[comp],
                "representative": graph.nodes[comp].get("representative"),
                "depth_min": mn,
                "depth_max": mx,
                "depth_spread": None if mn is None or mx is None else mx - mn,
                "root_contrib_limit": root_contrib_limit,
                "bounded_root_contributions": bounded_root_contribs(
                    graph,
                    roots=roots,
                    order_from_roots=order_from_roots,
                    dst=comp,
                    limit=root_contrib_limit,
                ),
                "labels": ["overlay:arango_dag", "role:capstone_summary"],
            }
        )
    return docs


def skeleton_docs(
    graph: QuotientGraph,
    *,
    run_id: str,
    limit: int,
    min_vulnerability: int,
) -> list[dict[str, Any]]:
    candidates = []
    for i, row in enumerate(graph.nodes):
        rep = row.get("representative")
        if not rep:
            continue
        member_count = int(row.get("member_count") or 1)
        score = len(graph.preds[i]) * member_count
        if len(graph.preds[i]) >= min_vulnerability:
            candidates.append((score, i))
    candidates.sort(reverse=True)
    docs = []
    for rank, (score, i) in enumerate(candidates[:limit]):
        docs.append(
            {
                "_key": f"skeleton_{rank}_{graph.keys[i]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "rank": rank,
                "component_key": graph.keys[i],
                "source_id": graph.ids[i],
                "representative": graph.nodes[i].get("representative"),
                "member_count": graph.nodes[i].get("member_count"),
                "score": score,
                "vulnerability_sources_proxy": len(graph.preds[i]),
                "dependency_targets": len(graph.forward[i]),
                "labels": ["overlay:arango_dag", "role:theory_skeleton"],
            }
        )
    return docs


def layer_flow_docs(graph: QuotientGraph, *, run_id: str) -> list[dict[str, Any]]:
    grouped: dict[tuple[str | None, str | None, str], dict[str, int]] = {}
    for (src, dst), multiplicity in graph.edge_multiplicity.items():
        src_layer = graph.dominant_layer[src]
        dst_layer = graph.dominant_layer[dst]
        polarity = flow_polarity(graph.dominant_depth[src], graph.dominant_depth[dst])
        key = (src_layer, dst_layer, polarity)
        row = grouped.setdefault(key, {"edge_count": 0, "multiplicity": 0, "witness_count": 0})
        row["edge_count"] += 1
        row["multiplicity"] += multiplicity
        row["witness_count"] += graph.edge_witness_counts.get((src, dst), 0)

    docs = []
    for idx, ((src_layer, dst_layer, polarity), vals) in enumerate(
        sorted(grouped.items(), key=lambda item: (str(item[0][0]), str(item[0][1]), item[0][2]))
    ):
        src_label = src_layer or "unlabeled"
        dst_label = dst_layer or "unlabeled"
        docs.append(
            {
                "_key": f"flow_{idx}_{src_label}_to_{dst_label}_{polarity}",
                "schema": SCHEMA,
                "run_id": run_id,
                "source_layer": src_layer,
                "target_layer": dst_layer,
                "source_depth": layer_depth(src_layer),
                "target_depth": layer_depth(dst_layer),
                "layer_flow": None if src_layer is None or dst_layer is None else f"{src_layer}->{dst_layer}",
                "flow_polarity": polarity,
                "regressive": polarity == "regressive",
                "edge_count": vals["edge_count"],
                "multiplicity": vals["multiplicity"],
                "witness_count": vals["witness_count"],
                "labels": ["overlay:arango_dag", "role:layer_flow"],
            }
        )
    return docs


def sources_sinks_docs(
    graph: QuotientGraph,
    *,
    roots: list[int],
    capstones: list[int],
    depth_min: list[int | None],
    depth_max: list[int | None],
    run_id: str,
) -> list[dict[str, Any]]:
    root_set = set(roots)
    capstone_set = set(capstones)
    docs = []
    for i in sorted(root_set | capstone_set):
        roles = []
        if i in root_set:
            roles.append("dependency_root")
        if i in capstone_set:
            roles.append("capstone")
        docs.append(
            {
                "_key": f"source_sink_{graph.keys[i]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "component_key": graph.keys[i],
                "source_id": graph.ids[i],
                "representative": graph.nodes[i].get("representative"),
                "roles": roles,
                "is_dependency_root": i in root_set,
                "is_capstone": i in capstone_set,
                "in_degree": len(graph.preds[i]),
                "out_degree": len(graph.forward[i]),
                "depth_min_from_dependency_roots": depth_min[i],
                "depth_max_from_dependency_roots": depth_max[i],
                "dominant_rep_layer": graph.dominant_layer[i],
                "labels": ["overlay:arango_dag", "role:source_sink"],
            }
        )
    return docs


def impact_docs(
    graph: QuotientGraph,
    *,
    seed: int | None,
    seed_down_dist: list[int | None] | None,
    seed_up_dist: list[int | None] | None,
    seed_down_paths: list[int] | None,
    seed_up_paths: list[int] | None,
    run_id: str,
    limit: int,
) -> list[dict[str, Any]]:
    if seed is None or seed_down_dist is None or seed_up_dist is None:
        return []
    rows = []
    for direction, dist, paths in [
        ("forward_impact", seed_down_dist, seed_down_paths or [0] * len(graph.nodes)),
        ("reverse_impact", seed_up_dist, seed_up_paths or [0] * len(graph.nodes)),
    ]:
        reached = [i for i, d in enumerate(dist) if d is not None]
        reached.sort(key=lambda i: (dist[i] or 0, -(paths[i] if i < len(paths) else 0), graph.nodes[i].get("representative") or ""))
        rows.append(
            {
                "_key": f"impact_summary_{direction}_{graph.keys[seed]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "seed_key": graph.keys[seed],
                "seed_id": graph.ids[seed],
                "seed_representative": graph.nodes[seed].get("representative"),
                "direction": direction,
                "reachable_count": len(reached),
                "path_sum": sum(paths),
                "max_distance": max((d for d in dist if d is not None), default=None),
                "labels": ["overlay:arango_dag", "role:impact_summary"],
            }
        )
        for rank, i in enumerate(reached[:limit]):
            rows.append(
                {
                    "_key": f"impact_{direction}_{rank}_{graph.keys[seed]}_{graph.keys[i]}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "seed_key": graph.keys[seed],
                    "component_key": graph.keys[i],
                    "source_id": graph.ids[i],
                    "representative": graph.nodes[i].get("representative"),
                    "direction": direction,
                    "rank": rank,
                    "distance": dist[i],
                    "path_count": paths[i] if i < len(paths) else None,
                    "dominant_rep_layer": graph.dominant_layer[i],
                    "labels": ["overlay:arango_dag", "role:impact_row"],
                }
            )
    return rows


def process_flow_docs(graph: QuotientGraph, *, run_id: str, limit: int) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    rows = []
    defects = []
    for idx, ((src, dst), multiplicity) in enumerate(sorted(graph.edge_multiplicity.items())):
        if idx >= limit:
            break
        src_depth = graph.dominant_depth[src]
        dst_depth = graph.dominant_depth[dst]
        src_capstone = len(graph.preds[src]) == 0
        # The SCC quotient may merge type/value evidence. Use the CLI-selected
        # edge kind when present; otherwise preserve the mixed/unknown status.
        edge_kind = None
        role = process_dependency_role(src_depth, dst_depth, edge_kind)
        polarity = flow_polarity(src_depth, dst_depth)
        locality = process_locality_class(src_depth, dst_depth)
        boundary = process_boundary_class(src_depth, dst_depth, role, src_capstone)
        tags = process_defect_tags(
            src_depth=src_depth,
            dst_depth=dst_depth,
            src_capstone=src_capstone,
            role=role,
            boundary=boundary,
            polarity=polarity,
            edge_kind=edge_kind,
        )
        key = f"flow_{graph.keys[src]}__to__{graph.keys[dst]}"
        row = {
            "_key": key,
            "schema": SCHEMA,
            "run_id": run_id,
            "source_key": graph.keys[src],
            "target_key": graph.keys[dst],
            "source_id": graph.ids[src],
            "target_id": graph.ids[dst],
            "source_representative": graph.nodes[src].get("representative"),
            "target_representative": graph.nodes[dst].get("representative"),
            "edge_use": "unknown_or_mixed",
            "provenance_kind": "directObserved",
            "dependency_role": role,
            "boundary_class": boundary,
            "locality_class": locality,
            "polarity_class": polarity,
            "source_layer": graph.dominant_layer[src],
            "target_layer": graph.dominant_layer[dst],
            "source_depth": src_depth,
            "target_depth": dst_depth,
            "defect_tags": tags,
            "defect_cost": defect_cost(tags),
            "multiplicity": multiplicity,
            "witness_count": graph.edge_witness_counts.get((src, dst), 0),
            "labels": ["overlay:arango_dag", "role:process_flow"],
        }
        rows.append(row)
        for tag in tags:
            defects.append(
                {
                    "_key": f"defect_{tag}_{key}"[:250],
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "locus": "edge",
                    "source_key": graph.keys[src],
                    "target_key": graph.keys[dst],
                    "source_representative": graph.nodes[src].get("representative"),
                    "target_representative": graph.nodes[dst].get("representative"),
                    "defect_kind": tag,
                    "cost": PROCESS_DEFECT_SEVERITY.get(tag, 1),
                    "flow_key": key,
                    "labels": ["overlay:arango_dag", "role:process_defect"],
                }
            )
    return rows, defects


def lawful_path_docs(
    graph: QuotientGraph,
    *,
    process_rows: list[dict[str, Any]],
    run_id: str,
    limit: int,
) -> list[dict[str, Any]]:
    by_edge = {(row["source_key"], row["target_key"]): row for row in process_rows}
    by_src: dict[str, list[dict[str, Any]]] = {}
    for row in process_rows:
        by_src.setdefault(str(row["source_key"]), []).append(row)
    docs = []
    for row in process_rows:
        if len(docs) >= limit:
            break
        if int(row.get("defect_cost") or 0) <= 1:
            docs.append(
                {
                    "_key": f"path_direct_{row['_key']}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "path_kind": "direct",
                    "source_key": row["source_key"],
                    "target_key": row["target_key"],
                    "step_flow_keys": [row["_key"]],
                    "total_defect_cost": row.get("defect_cost"),
                    "defects": row.get("defect_tags"),
                    "labels": ["overlay:arango_dag", "role:lawful_path_candidate"],
                }
            )
    for first in process_rows:
        if len(docs) >= limit:
            break
        for second in by_src.get(str(first["target_key"]), []):
            if len(docs) >= limit:
                break
            total_cost = int(first.get("defect_cost") or 0) + int(second.get("defect_cost") or 0)
            if total_cost <= 2:
                docs.append(
                    {
                        "_key": f"path_two_step_{first['_key']}__{second['_key']}"[:250],
                        "schema": SCHEMA,
                        "run_id": run_id,
                        "path_kind": "two_step",
                        "source_key": first["source_key"],
                        "mid_key": first["target_key"],
                        "target_key": second["target_key"],
                        "step_flow_keys": [first["_key"], second["_key"]],
                        "total_defect_cost": total_cost,
                        "defects": list(dict.fromkeys((first.get("defect_tags") or []) + (second.get("defect_tags") or []))),
                        "labels": ["overlay:arango_dag", "role:lawful_path_candidate"],
                    }
                )
    return docs


def wl_label_docs(graph: QuotientGraph, *, run_id: str, rounds: int, limit: int) -> list[dict[str, Any]]:
    labels = [
        stable_hash(
            {
                "layer": graph.dominant_layer[i],
                "depth": graph.dominant_depth[i],
                "member_count": int(graph.nodes[i].get("member_count") or 1),
                "out_degree": len(graph.forward[i]),
                "in_degree": len(graph.preds[i]),
            }
        )
        for i in range(len(graph.nodes))
    ]
    for _ in range(rounds):
        next_labels = []
        for i, current in enumerate(labels):
            neigh = sorted((labels[j], "out") for j in graph.forward[i])
            neigh += sorted((labels[j], "in") for j in graph.preds[i])
            next_labels.append(stable_hash({"self": current, "neighbors": neigh}))
        labels = next_labels
    docs = []
    for i in range(min(limit, len(labels))):
        docs.append(
            {
                "_key": f"wl_{graph.keys[i]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "component_key": graph.keys[i],
                "source_id": graph.ids[i],
                "representative": graph.nodes[i].get("representative"),
                "rounds": rounds,
                "wl_hash": labels[i],
                "dominant_rep_layer": graph.dominant_layer[i],
                "labels": ["overlay:arango_dag", "role:wl_hash"],
            }
        )
    return docs


MOTIFS: dict[str, tuple[int, tuple[tuple[int, int], ...]]] = {
    "CommutativeSquare": (4, ((0, 1), (0, 2), (1, 3), (2, 3))),
    "Diamond": (4, ((0, 1), (0, 2), (1, 3), (2, 3))),
    "Span": (3, ((0, 2), (1, 2))),
    "Cospan": (3, ((2, 0), (2, 1))),
    "Triangle": (3, ((0, 1), (1, 2), (0, 2))),
    "Fork": (4, ((0, 1), (0, 2), (0, 3))),
}


def has_edge(edge_set: set[tuple[int, int]], u: int, v: int) -> bool:
    return (u, v) in edge_set


def motif_docs(
    graph: QuotientGraph,
    *,
    run_id: str,
    seed: int | None,
    radius: int,
    max_nodes: int,
    max_results_per_motif: int,
) -> list[dict[str, Any]]:
    if seed is None:
        candidates = set(range(min(max_nodes, len(graph.nodes))))
    else:
        down = bfs_dist(graph.forward, [seed])
        up = bfs_dist(graph.preds, [seed])
        candidates = {
            i
            for i in range(len(graph.nodes))
            if (down[i] is not None and down[i] <= radius) or (up[i] is not None and up[i] <= radius)
        }
        if len(candidates) > max_nodes:
            ranked = sorted(candidates, key=lambda i: (min(x for x in [down[i], up[i]] if x is not None), -len(graph.preds[i])))
            candidates = set(ranked[:max_nodes])

    edge_set = {(u, v) for (u, v) in graph.edge_multiplicity if u in candidates and v in candidates}
    docs = []
    for motif_name, (num_nodes, edges) in MOTIFS.items():
        results = 0
        if motif_name in {"Span", "Cospan"}:
            for c in candidates:
                neigh = graph.preds[c] if motif_name == "Span" else graph.forward[c]
                neigh = [x for x in neigh if x in candidates]
                for a_idx in range(len(neigh)):
                    for b_idx in range(a_idx + 1, len(neigh)):
                        if results >= max_results_per_motif:
                            break
                        mapping = [neigh[a_idx], neigh[b_idx], c] if motif_name == "Span" else [neigh[a_idx], neigh[b_idx], c]
                        docs.append(motif_row(graph, run_id, motif_name, mapping, results))
                        results += 1
                    if results >= max_results_per_motif:
                        break
                if results >= max_results_per_motif:
                    break
        elif motif_name in {"Triangle"}:
            for a, b in edge_set:
                for c in graph.forward[b]:
                    if c in candidates and has_edge(edge_set, a, c):
                        docs.append(motif_row(graph, run_id, motif_name, [a, b, c], results))
                        results += 1
                        if results >= max_results_per_motif:
                            break
                if results >= max_results_per_motif:
                    break
        elif motif_name in {"Fork"}:
            for a in candidates:
                outs = [x for x in graph.forward[a] if x in candidates]
                for i in range(len(outs)):
                    for j in range(i + 1, len(outs)):
                        for k in range(j + 1, len(outs)):
                            docs.append(motif_row(graph, run_id, motif_name, [a, outs[i], outs[j], outs[k]], results))
                            results += 1
                            if results >= max_results_per_motif:
                                break
                        if results >= max_results_per_motif:
                            break
                    if results >= max_results_per_motif:
                        break
                if results >= max_results_per_motif:
                    break
        else:
            # Square/diamond: a -> b,c and b,c -> d.
            for a in candidates:
                outs = [x for x in graph.forward[a] if x in candidates]
                for i in range(len(outs)):
                    b = outs[i]
                    for c in outs[i + 1 :]:
                        common = [d for d in graph.forward[b] if d in candidates and has_edge(edge_set, c, d)]
                        for d in common:
                            docs.append(motif_row(graph, run_id, motif_name, [a, b, c, d], results))
                            results += 1
                            if results >= max_results_per_motif:
                                break
                        if results >= max_results_per_motif:
                            break
                    if results >= max_results_per_motif:
                        break
                if results >= max_results_per_motif:
                    break
    return docs


def motif_row(graph: QuotientGraph, run_id: str, motif_name: str, mapping: list[int], idx: int) -> dict[str, Any]:
    return {
        "_key": f"motif_{motif_name}_{idx}_{'_'.join(graph.keys[i] for i in mapping)}"[:250],
        "schema": SCHEMA,
        "run_id": run_id,
        "motif": motif_name,
        "mapping_keys": [graph.keys[i] for i in mapping],
        "mapping_ids": [graph.ids[i] for i in mapping],
        "representatives": [graph.nodes[i].get("representative") for i in mapping],
        "layers": [graph.dominant_layer[i] for i in mapping],
        "labels": ["overlay:arango_dag", "role:motif_match"],
    }


def induced_subgraph(graph: QuotientGraph, seed: int | None, radius: int, max_nodes: int) -> tuple[list[int], dict[int, int]]:
    if seed is None:
        nodes = list(range(min(max_nodes, len(graph.nodes))))
    else:
        down = bfs_dist(graph.forward, [seed])
        up = bfs_dist(graph.preds, [seed])
        nodes = [
            i
            for i in range(len(graph.nodes))
            if (down[i] is not None and down[i] <= radius) or (up[i] is not None and up[i] <= radius)
        ]
        nodes.sort(key=lambda i: (min(x for x in [down[i], up[i]] if x is not None), graph.nodes[i].get("representative") or ""))
        nodes = nodes[:max_nodes]
    return nodes, {old: new for new, old in enumerate(nodes)}


def rank_mod2(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    rank = 0
    for x in rows:
        v = x
        while v:
            p = v.bit_length() - 1
            if p not in basis:
                basis[p] = v
                rank += 1
                break
            v ^= basis[p]
    return rank


def bounded_two_complex_docs(
    graph: QuotientGraph,
    *,
    run_id: str,
    seed: int | None,
    radius: int,
    max_nodes: int,
    max_edges: int,
    cell_limit: int,
) -> list[dict[str, Any]]:
    nodes, idx = induced_subgraph(graph, seed, radius, max_nodes)
    local_edges = []
    edge_index = {}
    for u in nodes:
        for v in graph.forward[u]:
            if v in idx:
                key = (idx[u], idx[v])
                edge_index[key] = len(local_edges)
                local_edges.append(key)
                if len(local_edges) > max_edges:
                    return [
                        {
                            "_key": "two_complex_summary",
                            "schema": SCHEMA,
                            "run_id": run_id,
                            "computed": False,
                            "reason": "edge_limit_exceeded",
                            "vertices": len(nodes),
                            "edge_limit": max_edges,
                            "labels": ["overlay:arango_dag", "role:two_complex_summary"],
                        }
                    ]

    faces = []
    for (u, v), e_uv in edge_index.items():
        for old_w in graph.forward[nodes[v]]:
            if old_w not in idx:
                continue
            w = idx[old_w]
            e_vw = edge_index.get((v, w))
            e_uw = edge_index.get((u, w))
            if e_vw is not None and e_uw is not None:
                faces.append((e_uv, e_vw, e_uw))
    digons = []
    for (u, v), e_uv in edge_index.items():
        e_vu = edge_index.get((v, u))
        if e_vu is not None and e_uv < e_vu:
            digons.append((e_uv, e_vu))

    boundary1_rows = []
    for u, v in local_edges:
        boundary1_rows.append((1 << u) ^ (1 << v))
    boundary2_rows = []
    for a, b, c in faces:
        boundary2_rows.append((1 << a) ^ (1 << b) ^ (1 << c))
    for a, b in digons:
        boundary2_rows.append((1 << a) ^ (1 << b))
    r1 = rank_mod2(boundary1_rows)
    r2 = rank_mod2(boundary2_rows)
    b0 = len(nodes) - r1
    b1 = len(local_edges) - r1 - r2
    euler = len(nodes) - len(local_edges) + len(faces) + len(digons)
    boundary_squared_zero = True
    for row in boundary2_rows:
        accum = 0
        x = row
        while x:
            bit = x & -x
            e_idx = bit.bit_length() - 1
            accum ^= boundary1_rows[e_idx]
            x ^= bit
        if accum != 0:
            boundary_squared_zero = False
            break
    cell_rows: list[dict[str, Any]] = []
    if cell_limit > 0:
        for local_idx, (u, v) in enumerate(local_edges[:cell_limit]):
            src = nodes[u]
            dst = nodes[v]
            cell_rows.append(
                {
                    "_key": f"tc_edge_{local_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "cell_kind": "edge",
                    "local_edge_index": local_idx,
                    "local_boundary1_vertices": [u, v],
                    "component_keys": [graph.keys[src], graph.keys[dst]],
                    "component_ids": [graph.ids[src], graph.ids[dst]],
                    "representatives": [graph.nodes[src].get("representative"), graph.nodes[dst].get("representative")],
                    "labels": ["overlay:arango_dag", "role:two_complex_cell", "cell:edge"],
                }
            )
        remaining = max(cell_limit - len(cell_rows), 0)
        for face_idx, (a, b, c) in enumerate(faces[:remaining]):
            cell_rows.append(
                {
                    "_key": f"tc_face_tri_{face_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "cell_kind": "triangular_face",
                    "local_face_index": face_idx,
                    "local_boundary2_edges": [a, b, c],
                    "labels": ["overlay:arango_dag", "role:two_complex_cell", "cell:face", "face:triangle"],
                }
            )
        remaining = max(cell_limit - len(cell_rows), 0)
        for digon_idx, (a, b) in enumerate(digons[:remaining]):
            cell_rows.append(
                {
                    "_key": f"tc_face_digon_{digon_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "cell_kind": "digon_face",
                    "local_face_index": digon_idx,
                    "local_boundary2_edges": [a, b],
                    "labels": ["overlay:arango_dag", "role:two_complex_cell", "cell:face", "face:digon"],
                }
            )

    summary = {
            "_key": "two_complex_summary",
            "schema": SCHEMA,
            "run_id": run_id,
            "computed": True,
            "seed": None if seed is None else graph.ids[seed],
            "radius": radius,
            "vertices": len(nodes),
            "edges": len(local_edges),
            "triangular_faces": len(faces),
            "digon_faces": len(digons),
            "euler_characteristic": euler,
            "rank_boundary1_mod2": r1,
            "rank_boundary2_mod2": r2,
            "betti0_mod2": b0,
            "betti1_mod2": b1,
            "boundary_squared_zero_mod2": boundary_squared_zero,
            "trace_laplacian0_proxy": 2 * len(local_edges),
            "dirac_dim_proxy": len(nodes) + len(local_edges),
            "cell_rows_materialized": len(cell_rows),
            "cell_row_limit": cell_limit,
            "cell_rows_truncated": len(cell_rows) < len(local_edges) + len(faces) + len(digons),
            "labels": ["overlay:arango_dag", "role:two_complex_summary", "field:mod2"],
        }
    return [summary] + cell_rows


def bounded_hodge_dirac_chiral_docs(
    graph: QuotientGraph,
    *,
    run_id: str,
    seed: int | None,
    radius: int,
    max_nodes: int,
    max_edges: int,
    sparse_limit: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    nodes, idx = induced_subgraph(graph, seed, radius, max_nodes)
    local_edges = []
    for u in nodes:
        for v in graph.forward[u]:
            if v in idx:
                local_edges.append((idx[u], idx[v]))
                if len(local_edges) > max_edges:
                    summary = {
                        "_key": "hodge_summary",
                        "schema": SCHEMA,
                        "run_id": run_id,
                        "computed": False,
                        "reason": "edge_limit_exceeded",
                        "vertices": len(nodes),
                        "edge_limit": max_edges,
                        "labels": ["overlay:arango_dag", "role:hodge_summary"],
                    }
                    return [summary], [], []

    degree = [0] * len(nodes)
    lap_entries: dict[tuple[int, int], int] = {}
    dirac_rows: list[dict[str, Any]] = []
    chiral_rows: list[dict[str, Any]] = []
    anticommute_violations = 0

    signs = []
    for local_i, old_i in enumerate(nodes):
        depth = graph.dominant_depth[old_i]
        sign = 1 if depth is None or depth % 2 == 0 else -1
        signs.append(sign)
        if len(chiral_rows) < sparse_limit:
            chiral_rows.append(
                {
                    "_key": f"chiral_vertex_{local_i}_{graph.keys[old_i]}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "cell_kind": "vertex",
                    "local_index": local_i,
                    "component_key": graph.keys[old_i],
                    "source_id": graph.ids[old_i],
                    "representative": graph.nodes[old_i].get("representative"),
                    "grading_source": "dominant_rep_depth_parity",
                    "sign": sign,
                    "labels": ["overlay:arango_dag", "role:chiral_grading"],
                }
            )

    for e_idx, (u, v) in enumerate(local_edges):
        degree[u] += 1
        degree[v] += 1
        lap_entries[(u, u)] = lap_entries.get((u, u), 0) + 1
        lap_entries[(v, v)] = lap_entries.get((v, v), 0) + 1
        lap_entries[(u, v)] = lap_entries.get((u, v), 0) - 1
        lap_entries[(v, u)] = lap_entries.get((v, u), 0) - 1

        edge_sign = -signs[v]
        if signs[u] + edge_sign != 0 or signs[v] + edge_sign != 0:
            anticommute_violations += 1
        if len(chiral_rows) < sparse_limit:
            chiral_rows.append(
                {
                    "_key": f"chiral_edge_{e_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "cell_kind": "edge",
                    "local_edge_index": e_idx,
                    "local_boundary1_vertices": [u, v],
                    "grading_source": "negative_target_vertex_sign",
                    "sign": edge_sign,
                    "anticommutation_local_ok": signs[u] + edge_sign == 0 and signs[v] + edge_sign == 0,
                    "labels": ["overlay:arango_dag", "role:chiral_grading"],
                }
            )
        if len(dirac_rows) + 2 < sparse_limit:
            n0 = len(nodes)
            dirac_rows.append(
                {
                    "_key": f"dirac_upper_{e_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "row": u,
                    "col": n0 + e_idx,
                    "value": -1,
                    "block": "delta0",
                    "labels": ["overlay:arango_dag", "role:dirac_sparse_entry"],
                }
            )
            dirac_rows.append(
                {
                    "_key": f"dirac_lower_{e_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "row": n0 + e_idx,
                    "col": u,
                    "value": -1,
                    "block": "boundary1",
                    "labels": ["overlay:arango_dag", "role:dirac_sparse_entry"],
                }
            )
            dirac_rows.append(
                {
                    "_key": f"dirac_upper_t_{e_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "row": v,
                    "col": n0 + e_idx,
                    "value": 1,
                    "block": "delta0",
                    "labels": ["overlay:arango_dag", "role:dirac_sparse_entry"],
                }
            )
            dirac_rows.append(
                {
                    "_key": f"dirac_lower_t_{e_idx}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "row": n0 + e_idx,
                    "col": v,
                    "value": 1,
                    "block": "boundary1",
                    "labels": ["overlay:arango_dag", "role:dirac_sparse_entry"],
                }
            )

    hodge_rows = [
        {
            "_key": "hodge_summary",
            "schema": SCHEMA,
            "run_id": run_id,
            "computed": True,
            "seed": None if seed is None else graph.ids[seed],
            "radius": radius,
            "vertices": len(nodes),
            "edges": len(local_edges),
            "laplacian0_sparse_entries": len(lap_entries),
            "trace_laplacian0": sum(degree),
            "dirac_dim": len(nodes) + len(local_edges),
            "chiral_anticommutation_violations": anticommute_violations,
            "sparse_entry_limit": sparse_limit,
            "labels": ["overlay:arango_dag", "role:hodge_summary"],
        }
    ]
    for idx_entry, ((row, col), val) in enumerate(sorted(lap_entries.items())[:sparse_limit]):
        hodge_rows.append(
            {
                "_key": f"lap0_{idx_entry}_{row}_{col}",
                "schema": SCHEMA,
                "run_id": run_id,
                "operator": "laplacian0",
                "row": row,
                "col": col,
                "value": val,
                "labels": ["overlay:arango_dag", "role:hodge_sparse_entry"],
            }
        )
    return hodge_rows, chiral_rows, dirac_rows


def dominator_docs(
    graph: QuotientGraph,
    *,
    masks: list[int],
    run_id: str,
    limit: int,
    include_mask_hex: bool,
) -> list[dict[str, Any]]:
    rows = []
    for i, mask in enumerate(masks[:limit]):
        rows.append(
            {
                "_key": f"dom_{graph.keys[i]}",
                "schema": SCHEMA,
                "run_id": run_id,
                "component_key": graph.keys[i],
                "source_id": graph.ids[i],
                "representative": graph.nodes[i].get("representative"),
                "strict_dominator_count": mask.bit_count() - 1,
                "self_included_dominator_count": mask.bit_count(),
                "dominator_mask_encoding": "integer_bitset_hex_by_topology_component_index" if include_mask_hex else None,
                "dominator_mask_hex": hex(mask) if include_mask_hex else None,
                "truncated": limit < len(masks),
                "labels": ["overlay:arango_dag", "role:dominator_set"],
            }
        )
    return rows


def import_batch(target: ArangoTarget, collection: str, rows: list[dict[str, Any]], *, batch_size: int) -> dict[str, Any]:
    created = updated = errors = 0
    for i in range(0, len(rows), batch_size):
        batch = rows[i : i + batch_size]
        out = request_json(
            "POST",
            db_url(target, f"/_api/document/{quote(collection)}?overwriteMode=replace&silent=false"),
            username=target.username,
            password=target.password,
            payload=batch,
        )
        if isinstance(out, list):
            for item in out:
                if isinstance(item, dict) and item.get("error"):
                    errors += 1
                elif isinstance(item, dict) and item.get("_oldRev"):
                    updated += 1
                else:
                    created += 1
        elif isinstance(out, dict) and out.get("error"):
            errors += len(batch)
        else:
            created += len(batch)
    return {"created": created, "updated": updated, "errors": errors, "total": len(rows)}


def prepare_collections(target: ArangoTarget, *, drop_existing: bool) -> None:
    specs = [
        CollectionSpec("arango_dag_components", False),
        CollectionSpec("arango_dag_component_edges", True),
        CollectionSpec("arango_dag_layers", False),
        CollectionSpec("arango_dag_chains", False),
        CollectionSpec("arango_dag_capstones", False),
        CollectionSpec("arango_dag_skeleton", False),
        CollectionSpec("arango_dag_layer_flows", False),
        CollectionSpec("arango_dag_dominators", False),
        CollectionSpec("arango_dag_wl_labels", False),
        CollectionSpec("arango_dag_motifs", False),
        CollectionSpec("arango_dag_two_complex", False),
        CollectionSpec("arango_dag_sources_sinks", False),
        CollectionSpec("arango_dag_impact", False),
        CollectionSpec("arango_dag_process_flows", False),
        CollectionSpec("arango_dag_defects", False),
        CollectionSpec("arango_dag_lawful_paths", False),
        CollectionSpec("arango_dag_hodge", False),
        CollectionSpec("arango_dag_chiral", False),
        CollectionSpec("arango_dag_dirac", False),
        CollectionSpec("arango_dag_morphism_candidates", False),
    ]
    ensure_database(target)
    existing = list_collections(target)
    for spec in specs:
        if spec.name in existing and drop_existing:
            drop_collection(target, spec.name)
            existing.remove(spec.name)
        if spec.name not in existing:
            create_collection(target, spec)


def graph_url(target: ArangoTarget, graph_name: str = "") -> str:
    suffix = f"/{quote(graph_name)}" if graph_name else ""
    return db_url(target, f"/_api/gharial{suffix}")


def graph_exists(target: ArangoTarget, graph_name: str) -> bool:
    try:
        out = request_json(
            "GET",
            graph_url(target, graph_name),
            username=target.username,
            password=target.password,
        )
        return isinstance(out, dict) and not out.get("error", False)
    except RuntimeError as exc:
        if "HTTP 404" in str(exc):
            return False
        raise


def drop_graph(target: ArangoTarget, graph_name: str) -> None:
    try:
        request_json(
            "DELETE",
            graph_url(target, graph_name) + "?dropCollections=false",
            username=target.username,
            password=target.password,
        )
    except RuntimeError as exc:
        if "HTTP 404" not in str(exc):
            raise


def ensure_named_graph(target: ArangoTarget, graph_name: str, *, replace: bool) -> dict[str, Any]:
    if replace and graph_exists(target, graph_name):
        drop_graph(target, graph_name)
    elif graph_exists(target, graph_name):
        return {"created": False, "graph_name": graph_name}

    result = request_json(
        "POST",
        graph_url(target),
        username=target.username,
        password=target.password,
        payload={
            "name": graph_name,
            "edgeDefinitions": [
                {
                    "collection": "arango_dag_component_edges",
                    "from": ["arango_dag_components"],
                    "to": ["arango_dag_components"],
                }
            ],
            "orphanCollections": [
                "arango_dag_layers",
                "arango_dag_chains",
                "arango_dag_capstones",
                "arango_dag_skeleton",
                "arango_dag_layer_flows",
                "arango_dag_dominators",
                "arango_dag_wl_labels",
                "arango_dag_motifs",
                "arango_dag_two_complex",
                "arango_dag_sources_sinks",
                "arango_dag_impact",
                "arango_dag_process_flows",
                "arango_dag_defects",
                "arango_dag_lawful_paths",
                "arango_dag_hodge",
                "arango_dag_chiral",
                "arango_dag_dirac",
                "arango_dag_morphism_candidates",
            ],
            "isSmart": False,
        },
    )
    return {
        "created": True,
        "graph_name": graph_name,
        "error": bool(result.get("error")) if isinstance(result, dict) else False,
    }


def two_complex_summary(graph: QuotientGraph, *, edge_limit: int) -> dict[str, Any]:
    edge_count = len(graph.edge_multiplicity)
    if edge_count > edge_limit:
        return {
            "computed": False,
            "reason": "edge_limit_exceeded",
            "edge_count": edge_count,
            "edge_limit": edge_limit,
        }
    edge_index = {edge: i for i, edge in enumerate(sorted(graph.edge_multiplicity))}
    digons = 0
    for (u, v), i in edge_index.items():
        j = edge_index.get((v, u))
        if j is not None and i < j:
            digons += 1
    triangles = 0
    for (u, v) in edge_index:
        for w in graph.forward[v]:
            if (u, w) in edge_index:
                triangles += 1
    return {
        "computed": True,
        "vertices": len(graph.nodes),
        "edges": edge_count,
        "triangular_faces": triangles,
        "digon_faces": digons,
        "euler_characteristic": len(graph.nodes) - edge_count + triangles + digons,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:8529")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--username", default="root")
    parser.add_argument("--password", default="")
    parser.add_argument("--overlay-nodes", default="topology_overlay")
    parser.add_argument("--overlay-edges", default="topology_overlay_edges")
    parser.add_argument("--edge-kind", choices=["type", "value"], default=None)
    parser.add_argument("--seed-scc", type=int, default=None)
    parser.add_argument("--seed-representative", default=None)
    parser.add_argument("--compute-dominators", action="store_true")
    parser.add_argument("--layer-preview-limit", type=int, default=25)
    parser.add_argument("--deepest-chain-limit", type=int, default=128)
    parser.add_argument("--capstone-limit", type=int, default=512)
    parser.add_argument("--capstone-root-contrib-limit", type=int, default=0)
    parser.add_argument("--skeleton-limit", type=int, default=500)
    parser.add_argument("--skeleton-min-vulnerability", type=int, default=1)
    parser.add_argument("--two-complex-edge-limit", type=int, default=200000)
    parser.add_argument("--wl-rounds", type=int, default=3)
    parser.add_argument("--wl-limit", type=int, default=5000)
    parser.add_argument("--motif-radius", type=int, default=2)
    parser.add_argument("--motif-max-nodes", type=int, default=1000)
    parser.add_argument("--motif-max-results-per-motif", type=int, default=200)
    parser.add_argument("--two-complex-radius", type=int, default=2)
    parser.add_argument("--two-complex-max-nodes", type=int, default=2000)
    parser.add_argument("--two-complex-max-edges", type=int, default=50000)
    parser.add_argument("--two-complex-cell-limit", type=int, default=10000)
    parser.add_argument("--dominator-limit", type=int, default=5000)
    parser.add_argument("--write-dominator-masks", action="store_true")
    parser.add_argument("--impact-limit", type=int, default=1000)
    parser.add_argument("--process-flow-limit", type=int, default=100000)
    parser.add_argument("--lawful-path-limit", type=int, default=5000)
    parser.add_argument("--hodge-sparse-limit", type=int, default=20000)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--drop-existing", action="store_true")
    parser.add_argument("--graph-name", default=DEFAULT_GRAPH_NAME)
    parser.add_argument("--create-named-graph", action="store_true")
    parser.add_argument("--batch-size", type=int, default=5000)
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/infotree/arango_dag_algorithms_report.json"))
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = ArangoTarget(
        endpoint=str(args.endpoint).rstrip("/"),
        database=str(args.database),
        username=str(args.username),
        password=str(args.password),
    )
    run_id = str(int(time.time()))
    t0 = time.perf_counter()
    graph = load_quotient_graph(
        target,
        overlay_nodes=str(args.overlay_nodes),
        overlay_edges=str(args.overlay_edges),
        edge_kind=args.edge_kind,
    )
    load_seconds = time.perf_counter() - t0

    t0 = time.perf_counter()
    order, cyclic_residue = topo(graph.forward, graph.preds)
    roots = [i for i, outs in enumerate(graph.forward) if not outs]
    capstones = [i for i, ins in enumerate(graph.preds) if not ins]
    depth_min = bfs_dist(graph.preds, roots)
    order_from_roots = list(reversed(order))
    depth_max, max_pred = dag_longest_depth_with_pred(graph.preds, order_from_roots, roots)
    seed = choose_seed(graph, args.seed_representative, args.seed_scc)
    seed_down_dist = seed_up_dist = seed_down_paths = seed_up_paths = None
    if seed is not None:
        seed_down_dist = bfs_dist(graph.forward, [seed])
        seed_up_dist = bfs_dist(graph.preds, [seed])
        seed_down_paths = path_counts(graph.forward, order, seed)
        seed_up_paths = path_counts(graph.preds, list(reversed(order)), seed)
    dom_masks = dominator_masks(graph.preds, order) if args.compute_dominators else None
    dom_counts = None if dom_masks is None else [mask.bit_count() - 1 for mask in dom_masks]
    algorithm_seconds = time.perf_counter() - t0

    tc_summary = two_complex_summary(graph, edge_limit=args.two_complex_edge_limit)
    component_rows = component_docs(
        graph,
        order=order,
        roots=roots,
        capstones=capstones,
        depth_min=depth_min,
        depth_max=depth_max,
        dom_counts=dom_counts,
        seed=seed,
        seed_down_dist=seed_down_dist,
        seed_up_dist=seed_up_dist,
        seed_down_paths=seed_down_paths,
        seed_up_paths=seed_up_paths,
        run_id=run_id,
    )
    edge_rows = component_edge_docs(graph, run_id=run_id)
    layer_rows = layer_docs(
        graph,
        depth_min=depth_min,
        run_id=run_id,
        node_preview_limit=int(args.layer_preview_limit),
    )
    chain_rows = deepest_chain_docs(
        graph,
        depth_max=depth_max,
        max_pred=max_pred,
        run_id=run_id,
        limit=int(args.deepest_chain_limit),
    )
    capstone_rows = capstone_docs(
        graph,
        capstones=capstones,
        roots=roots,
        depth_min=depth_min,
        depth_max=depth_max,
        run_id=run_id,
        capstone_limit=int(args.capstone_limit),
        root_contrib_limit=int(args.capstone_root_contrib_limit),
        order_from_roots=order_from_roots,
    )
    skeleton_rows = skeleton_docs(
        graph,
        run_id=run_id,
        limit=int(args.skeleton_limit),
        min_vulnerability=int(args.skeleton_min_vulnerability),
    )
    layer_flow_rows = layer_flow_docs(graph, run_id=run_id)
    dominator_rows = (
        []
        if dom_masks is None
        else dominator_docs(
            graph,
            masks=dom_masks,
            run_id=run_id,
            limit=int(args.dominator_limit),
            include_mask_hex=bool(args.write_dominator_masks),
        )
    )
    wl_rows = wl_label_docs(
        graph,
        run_id=run_id,
        rounds=int(args.wl_rounds),
        limit=int(args.wl_limit),
    )
    motif_rows = motif_docs(
        graph,
        run_id=run_id,
        seed=seed,
        radius=int(args.motif_radius),
        max_nodes=int(args.motif_max_nodes),
        max_results_per_motif=int(args.motif_max_results_per_motif),
    )
    bounded_two_complex_rows = bounded_two_complex_docs(
        graph,
        run_id=run_id,
        seed=seed,
        radius=int(args.two_complex_radius),
        max_nodes=int(args.two_complex_max_nodes),
        max_edges=int(args.two_complex_max_edges),
        cell_limit=int(args.two_complex_cell_limit),
    )
    source_sink_rows = sources_sinks_docs(
        graph,
        roots=roots,
        capstones=capstones,
        depth_min=depth_min,
        depth_max=depth_max,
        run_id=run_id,
    )
    impact_rows = impact_docs(
        graph,
        seed=seed,
        seed_down_dist=seed_down_dist,
        seed_up_dist=seed_up_dist,
        seed_down_paths=seed_down_paths,
        seed_up_paths=seed_up_paths,
        run_id=run_id,
        limit=int(args.impact_limit),
    )
    process_flow_rows, defect_rows = process_flow_docs(
        graph,
        run_id=run_id,
        limit=int(args.process_flow_limit),
    )
    lawful_path_rows = lawful_path_docs(
        graph,
        process_rows=process_flow_rows,
        run_id=run_id,
        limit=int(args.lawful_path_limit),
    )
    hodge_rows, chiral_rows, dirac_rows = bounded_hodge_dirac_chiral_docs(
        graph,
        run_id=run_id,
        seed=seed,
        radius=int(args.two_complex_radius),
        max_nodes=int(args.two_complex_max_nodes),
        max_edges=int(args.two_complex_max_edges),
        sparse_limit=int(args.hodge_sparse_limit),
    )
    morphism_candidate_rows: list[dict[str, Any]] = []

    write_report: dict[str, Any] | None = None
    if args.write:
        if args.drop_existing and args.create_named_graph and graph_exists(target, str(args.graph_name)):
            drop_graph(target, str(args.graph_name))
        prepare_collections(target, drop_existing=bool(args.drop_existing))
        write_report = {
            "arango_dag_components": import_batch(
                target,
                "arango_dag_components",
                component_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_component_edges": import_batch(
                target,
                "arango_dag_component_edges",
                edge_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_layers": import_batch(
                target,
                "arango_dag_layers",
                layer_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_chains": import_batch(
                target,
                "arango_dag_chains",
                chain_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_capstones": import_batch(
                target,
                "arango_dag_capstones",
                capstone_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_skeleton": import_batch(
                target,
                "arango_dag_skeleton",
                skeleton_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_layer_flows": import_batch(
                target,
                "arango_dag_layer_flows",
                layer_flow_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_dominators": import_batch(
                target,
                "arango_dag_dominators",
                dominator_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_wl_labels": import_batch(
                target,
                "arango_dag_wl_labels",
                wl_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_motifs": import_batch(
                target,
                "arango_dag_motifs",
                motif_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_two_complex": import_batch(
                target,
                "arango_dag_two_complex",
                bounded_two_complex_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_sources_sinks": import_batch(
                target,
                "arango_dag_sources_sinks",
                source_sink_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_impact": import_batch(
                target,
                "arango_dag_impact",
                impact_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_process_flows": import_batch(
                target,
                "arango_dag_process_flows",
                process_flow_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_defects": import_batch(
                target,
                "arango_dag_defects",
                defect_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_lawful_paths": import_batch(
                target,
                "arango_dag_lawful_paths",
                lawful_path_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_hodge": import_batch(
                target,
                "arango_dag_hodge",
                hodge_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_chiral": import_batch(
                target,
                "arango_dag_chiral",
                chiral_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_dirac": import_batch(
                target,
                "arango_dag_dirac",
                dirac_rows,
                batch_size=int(args.batch_size),
            ),
            "arango_dag_morphism_candidates": import_batch(
                target,
                "arango_dag_morphism_candidates",
                morphism_candidate_rows,
                batch_size=int(args.batch_size),
            ),
            "live_counts": {
                "arango_dag_components": collection_count(target, "arango_dag_components"),
                "arango_dag_component_edges": collection_count(target, "arango_dag_component_edges"),
                "arango_dag_layers": collection_count(target, "arango_dag_layers"),
                "arango_dag_chains": collection_count(target, "arango_dag_chains"),
                "arango_dag_capstones": collection_count(target, "arango_dag_capstones"),
                "arango_dag_skeleton": collection_count(target, "arango_dag_skeleton"),
                "arango_dag_layer_flows": collection_count(target, "arango_dag_layer_flows"),
                "arango_dag_dominators": collection_count(target, "arango_dag_dominators"),
                "arango_dag_wl_labels": collection_count(target, "arango_dag_wl_labels"),
                "arango_dag_motifs": collection_count(target, "arango_dag_motifs"),
                "arango_dag_two_complex": collection_count(target, "arango_dag_two_complex"),
                "arango_dag_sources_sinks": collection_count(target, "arango_dag_sources_sinks"),
                "arango_dag_impact": collection_count(target, "arango_dag_impact"),
                "arango_dag_process_flows": collection_count(target, "arango_dag_process_flows"),
                "arango_dag_defects": collection_count(target, "arango_dag_defects"),
                "arango_dag_lawful_paths": collection_count(target, "arango_dag_lawful_paths"),
                "arango_dag_hodge": collection_count(target, "arango_dag_hodge"),
                "arango_dag_chiral": collection_count(target, "arango_dag_chiral"),
                "arango_dag_dirac": collection_count(target, "arango_dag_dirac"),
                "arango_dag_morphism_candidates": collection_count(target, "arango_dag_morphism_candidates"),
            },
        }
        if args.create_named_graph:
            write_report["named_graph"] = ensure_named_graph(
                target,
                str(args.graph_name),
                replace=bool(args.drop_existing),
            )

    seed_report = None
    if seed is not None:
        down_reach = sum(1 for x in seed_down_dist or [] if x is not None)
        up_reach = sum(1 for x in seed_up_dist or [] if x is not None)
        seed_report = {
            "index": seed,
            "source_id": graph.ids[seed],
            "representative": graph.nodes[seed].get("representative"),
            "scc_id": graph.nodes[seed].get("scc_id"),
            "downstream_reachable": down_reach,
            "upstream_reachable": up_reach,
            "downstream_path_sum": None if seed_down_paths is None else sum(seed_down_paths),
            "upstream_path_sum": None if seed_up_paths is None else sum(seed_up_paths),
        }

    report: dict[str, Any] = {
        "schema": SCHEMA,
        "run_id": run_id,
        "source": {
            "database": target.database,
            "overlay_nodes": args.overlay_nodes,
            "overlay_edges": args.overlay_edges,
            "edge_kind": args.edge_kind,
        },
        "truth_status": "derived_overlay_not_lean_authority",
        "loaded": {
            "component_count": len(graph.nodes),
            "scc_quotient_row_count": len(graph.edge_rows),
            "dedup_quotient_edge_count": len(graph.edge_multiplicity),
            "labeled_component_count": sum(1 for x in graph.dominant_layer if x is not None),
            "unlabeled_component_count": sum(1 for x in graph.dominant_layer if x is None),
        },
        "algorithms": {
            "topological_order_count": len(order),
            "cyclic_residue_count": len(cyclic_residue),
            "dependency_root_count": len(roots),
            "capstone_count": len(capstones),
            "depth_min_max": max((d for d in depth_min if d is not None), default=None),
            "depth_max_max": max((d for d in depth_max if d is not None), default=None),
            "dominators_computed": dom_counts is not None,
            "two_complex": tc_summary,
            "seed": seed_report,
            "layer_rows": len(layer_rows),
            "deepest_chain_rows": len(chain_rows),
            "capstone_rows": len(capstone_rows),
            "skeleton_rows": len(skeleton_rows),
            "layer_flow_rows": len(layer_flow_rows),
            "regressive_layer_flow_rows": sum(1 for row in layer_flow_rows if row.get("regressive")),
            "regressive_component_edges": sum(1 for row in edge_rows if row.get("regressive")),
            "dominator_rows": len(dominator_rows),
            "dominator_masks_persisted": bool(args.write_dominator_masks),
            "wl_label_rows": len(wl_rows),
            "motif_rows": len(motif_rows),
            "bounded_two_complex_rows": len(bounded_two_complex_rows),
            "bounded_two_complex": bounded_two_complex_rows[0] if bounded_two_complex_rows else None,
            "source_sink_rows": len(source_sink_rows),
            "impact_rows": len(impact_rows),
            "process_flow_rows": len(process_flow_rows),
            "defect_rows": len(defect_rows),
            "lawful_path_rows": len(lawful_path_rows),
            "hodge_rows": len(hodge_rows),
            "hodge_summary": hodge_rows[0] if hodge_rows else None,
            "chiral_rows": len(chiral_rows),
            "dirac_rows": len(dirac_rows),
            "morphism_candidate_rows": len(morphism_candidate_rows),
            "bounded_limits": {
                "layer_preview_limit": args.layer_preview_limit,
                "deepest_chain_limit": args.deepest_chain_limit,
                "capstone_limit": args.capstone_limit,
                "capstone_root_contrib_limit": args.capstone_root_contrib_limit,
                "skeleton_limit": args.skeleton_limit,
                "skeleton_min_vulnerability": args.skeleton_min_vulnerability,
                "wl_rounds": args.wl_rounds,
                "wl_limit": args.wl_limit,
                "motif_radius": args.motif_radius,
                "motif_max_nodes": args.motif_max_nodes,
                "motif_max_results_per_motif": args.motif_max_results_per_motif,
                "two_complex_radius": args.two_complex_radius,
                "two_complex_max_nodes": args.two_complex_max_nodes,
                "two_complex_max_edges": args.two_complex_max_edges,
                "two_complex_cell_limit": args.two_complex_cell_limit,
                "dominator_limit": args.dominator_limit,
                "impact_limit": args.impact_limit,
                "process_flow_limit": args.process_flow_limit,
                "lawful_path_limit": args.lawful_path_limit,
                "hodge_sparse_limit": args.hodge_sparse_limit,
            },
        },
        "timing": {
            "load_seconds": round(load_seconds, 3),
            "algorithm_seconds": round(algorithm_seconds, 3),
        },
        "write": write_report,
    }

    out = args.json_out.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    print(f"Arango DAG algorithm report written: {out}")
    print(
        "Loaded "
        f"components={len(graph.nodes)} quotient_rows={len(graph.edge_rows)} "
        f"dedup_edges={len(graph.edge_multiplicity)}"
    )
    print(
        "Algorithms "
        f"topo={len(order)} cyclic_residue={len(cyclic_residue)} "
        f"roots={len(roots)} capstones={len(capstones)} "
        f"layers={len(layer_rows)} chains={len(chain_rows)} skeleton={len(skeleton_rows)} "
        f"layer_flows={len(layer_flow_rows)}"
    )
    if seed_report:
        print("Seed " + json.dumps(seed_report, ensure_ascii=True))
    if write_report:
        print("Write " + json.dumps(write_report["live_counts"], ensure_ascii=True))
    return 0 if not cyclic_residue else 2


if __name__ == "__main__":
    raise SystemExit(main())
