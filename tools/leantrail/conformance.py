#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.store import GraphStore
from tools.leantrail.adapters import (
    import_arango_json,
    import_graphml,
    import_neo4j_csv,
    load_snapshot,
)

_DEP_EDGE_KINDS = {"depends_type", "depends_value"}
_SNAPSHOT_FORMATS = ("snapshot", "graphml", "neo4j-csv", "arango-json")


@dataclass
class PathQuery:
    src: str
    dst: str
    lawful_only: bool = True
    state_policy: str = "any"


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _read_snapshot(path: Path, fmt: str) -> GraphSnapshot:
    if fmt == "snapshot":
        return load_snapshot(path)
    if fmt == "graphml":
        return import_graphml(path)
    if fmt == "neo4j-csv":
        return import_neo4j_csv(path)
    if fmt == "arango-json":
        return import_arango_json(path)
    raise ValueError(f"Unsupported format: {fmt}")


def _jaccard(lhs: set[str], rhs: set[str]) -> float:
    if not lhs and not rhs:
        return 1.0
    union = lhs | rhs
    if not union:
        return 1.0
    return len(lhs & rhs) / len(union)


def _pct_drift(base: int, cand: int) -> float:
    denom = max(1, base)
    return abs(cand - base) / denom


def _top_ids(rows: list[dict[str, Any]], limit: int) -> list[str]:
    out: list[str] = []
    for row in rows[:limit]:
        node = row.get("node")
        if not isinstance(node, dict):
            continue
        node_id = node.get("id")
        if isinstance(node_id, str) and node_id:
            out.append(node_id)
    return out


def _edge_key(edge: Any) -> tuple[str, str, str, float, str]:
    return (edge.src, edge.dst, edge.kind, float(edge.weight), edge.evidence_ref)


def _compute_scc_signature(snapshot: GraphSnapshot) -> dict[str, Any]:
    node_ids = {node.id for node in snapshot.nodes}
    adjacency: dict[str, list[str]] = {nid: [] for nid in node_ids}

    for edge in snapshot.edges:
        if edge.kind not in _DEP_EDGE_KINDS:
            continue
        if edge.src in adjacency and edge.dst in node_ids:
            adjacency[edge.src].append(edge.dst)

    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    component_sizes: list[int] = []

    sys.setrecursionlimit(max(10000, len(node_ids) * 2 + 1000))

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in adjacency.get(v, []):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            size = 0
            while True:
                w = stack.pop()
                on_stack.remove(w)
                size += 1
                if w == v:
                    break
            component_sizes.append(size)

    for v in adjacency:
        if v not in indices:
            strongconnect(v)

    component_sizes.sort(reverse=True)
    return {
        "component_count": len(component_sizes),
        "largest_component": component_sizes[0] if component_sizes else 0,
        "top_components": component_sizes[:10],
    }


def _default_path_queries() -> list[PathQuery]:
    return [
        PathQuery(
            src="InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift",
            dst="InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift_cocycle",
            lawful_only=True,
            state_policy="any",
        ),
        PathQuery(
            src="InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity",
            dst="InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_cocycle",
            lawful_only=True,
            state_policy="any",
        ),
        PathQuery(
            src="InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential",
            dst="InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_cocycle",
            lawful_only=True,
            state_policy="any",
        ),
    ]


def _load_path_queries(path: Path | None) -> list[PathQuery]:
    if path is None:
        return _default_path_queries()

    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, list):
        raise ValueError("Path query file must be a JSON list")

    rows: list[PathQuery] = []
    for idx, row in enumerate(payload):
        if not isinstance(row, dict):
            raise ValueError(f"Path query row {idx} is not an object")
        src = row.get("from")
        dst = row.get("to")
        lawful = row.get("lawful_only", True)
        state_policy = str(row.get("state_policy", "any")).strip() or "any"
        if not isinstance(src, str) or not src:
            raise ValueError(f"Path query row {idx} has invalid 'from'")
        if not isinstance(dst, str) or not dst:
            raise ValueError(f"Path query row {idx} has invalid 'to'")
        if not isinstance(lawful, bool):
            raise ValueError(f"Path query row {idx} has non-bool 'lawful_only'")
        if state_policy not in {"any", "exclude-failed", "locked-only"}:
            raise ValueError(f"Path query row {idx} has invalid 'state_policy'")
        rows.append(PathQuery(src=src, dst=dst, lawful_only=lawful, state_policy=state_policy))
    return rows


def _load_required_locked_paths(path: Path | None) -> list[PathQuery]:
    if path is None:
        return []
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, list):
        raise ValueError("Required locked path file must be a JSON list")
    rows: list[PathQuery] = []
    for idx, row in enumerate(payload):
        if not isinstance(row, dict):
            raise ValueError(f"Required locked path row {idx} is not an object")
        src = row.get("from")
        dst = row.get("to")
        lawful = row.get("lawful_only", True)
        state_policy = str(row.get("state_policy", "locked-only")).strip() or "locked-only"
        if not isinstance(src, str) or not src:
            raise ValueError(f"Required locked path row {idx} has invalid 'from'")
        if not isinstance(dst, str) or not dst:
            raise ValueError(f"Required locked path row {idx} has invalid 'to'")
        if not isinstance(lawful, bool):
            raise ValueError(f"Required locked path row {idx} has non-bool 'lawful_only'")
        if state_policy not in {"any", "exclude-failed", "locked-only"}:
            raise ValueError(f"Required locked path row {idx} has invalid 'state_policy'")
        rows.append(PathQuery(src=src, dst=dst, lawful_only=lawful, state_policy=state_policy))
    return rows


def _render_md(report: dict[str, Any]) -> str:
    checks = report.get("checks", [])
    lines = [
        "# LeanTrail Conformance Report",
        "",
        f"- Created: `{report.get('created_at', '')}`",
        f"- Baseline: `{report.get('baseline', '')}` ({report.get('baseline_format', 'snapshot')})",
        f"- Candidate: `{report.get('candidate', '')}` ({report.get('candidate_format', 'snapshot')})",
        f"- Overall pass: `{report.get('overall_pass', False)}`",
        "",
        "## Checks",
        "",
        "| Check | Pass | Details |",
        "|---|---|---|",
    ]
    for row in checks:
        name = str(row.get("name", ""))
        passed = bool(row.get("pass", False))
        details = row.get("details", {})
        compact = json.dumps(details, ensure_ascii=True, sort_keys=True)
        if len(compact) > 240:
            compact = compact[:237] + "..."
        lines.append(f"| `{name}` | `{passed}` | `{compact}` |")

    summary = report.get("summary", {})
    if isinstance(summary, dict):
        lines.extend(
            [
                "",
                "## Summary",
                "",
                "```json",
                json.dumps(summary, indent=2, ensure_ascii=True),
                "```",
            ]
        )
    return "\n".join(lines) + "\n"


def run_conformance(
    *,
    baseline_path: Path,
    baseline_format: str,
    candidate_path: Path,
    candidate_format: str,
    query_file: Path | None,
    required_locked_paths_file: Path | None,
    hotspot_limit: int,
    max_node_drift_pct: float,
    max_edge_drift_pct: float,
    min_path_match_ratio: float,
    min_coherence_jaccard: float,
    min_holonomy_jaccard: float,
    require_same_toolchain: bool,
) -> dict[str, Any]:
    baseline = _read_snapshot(baseline_path, baseline_format)
    candidate = _read_snapshot(candidate_path, candidate_format)

    base_store = GraphStore(baseline)
    cand_store = GraphStore(candidate)

    checks: list[dict[str, Any]] = []

    base_nodes = len(baseline.nodes)
    cand_nodes = len(candidate.nodes)
    node_drift = _pct_drift(base_nodes, cand_nodes)
    checks.append(
        {
            "name": "node_count_drift",
            "pass": node_drift <= max_node_drift_pct,
            "details": {
                "baseline": base_nodes,
                "candidate": cand_nodes,
                "drift_pct": node_drift,
                "max_allowed": max_node_drift_pct,
            },
        }
    )

    base_edges = len(baseline.edges)
    cand_edges = len(candidate.edges)
    edge_drift = _pct_drift(base_edges, cand_edges)
    checks.append(
        {
            "name": "edge_count_drift",
            "pass": edge_drift <= max_edge_drift_pct,
            "details": {
                "baseline": base_edges,
                "candidate": cand_edges,
                "drift_pct": edge_drift,
                "max_allowed": max_edge_drift_pct,
            },
        }
    )

    base_node_kind = Counter(node.kind for node in baseline.nodes)
    cand_node_kind = Counter(node.kind for node in candidate.nodes)
    kind_rows: dict[str, dict[str, float | int]] = {}
    for kind in sorted(set(base_node_kind) | set(cand_node_kind)):
        base_n = int(base_node_kind.get(kind, 0))
        cand_n = int(cand_node_kind.get(kind, 0))
        kind_rows[kind] = {
            "baseline": base_n,
            "candidate": cand_n,
            "drift_pct": _pct_drift(base_n, cand_n),
        }
    checks.append(
        {
            "name": "node_kind_counts",
            "pass": True,
            "details": kind_rows,
        }
    )

    base_edge_kind = Counter(edge.kind for edge in baseline.edges)
    cand_edge_kind = Counter(edge.kind for edge in candidate.edges)
    edge_kind_rows: dict[str, dict[str, float | int]] = {}
    for kind in sorted(set(base_edge_kind) | set(cand_edge_kind)):
        base_n = int(base_edge_kind.get(kind, 0))
        cand_n = int(cand_edge_kind.get(kind, 0))
        edge_kind_rows[kind] = {
            "baseline": base_n,
            "candidate": cand_n,
            "drift_pct": _pct_drift(base_n, cand_n),
        }
    checks.append(
        {
            "name": "edge_kind_counts",
            "pass": True,
            "details": edge_kind_rows,
        }
    )

    base_node_ids = {node.id for node in baseline.nodes}
    cand_node_ids = {node.id for node in candidate.nodes}
    missing_nodes = sorted(base_node_ids - cand_node_ids)
    extra_nodes = sorted(cand_node_ids - base_node_ids)
    checks.append(
        {
            "name": "node_id_overlap",
            "pass": not missing_nodes,
            "details": {
                "baseline_only_count": len(missing_nodes),
                "candidate_only_count": len(extra_nodes),
                "baseline_only_sample": missing_nodes[:20],
                "candidate_only_sample": extra_nodes[:20],
            },
        }
    )

    base_edge_keys = {_edge_key(edge) for edge in baseline.edges}
    cand_edge_keys = {_edge_key(edge) for edge in candidate.edges}
    missing_edges = sorted(base_edge_keys - cand_edge_keys)
    extra_edges = sorted(cand_edge_keys - base_edge_keys)
    checks.append(
        {
            "name": "edge_key_overlap",
            "pass": not missing_edges,
            "details": {
                "baseline_only_count": len(missing_edges),
                "candidate_only_count": len(extra_edges),
                "baseline_only_sample": [list(x) for x in missing_edges[:20]],
                "candidate_only_sample": [list(x) for x in extra_edges[:20]],
            },
        }
    )

    if require_same_toolchain:
        base_toolchain = str(baseline.metadata.get("toolchain", ""))
        cand_toolchain = str(candidate.metadata.get("toolchain", ""))
        checks.append(
            {
                "name": "toolchain_match",
                "pass": base_toolchain == cand_toolchain,
                "details": {
                    "baseline": base_toolchain,
                    "candidate": cand_toolchain,
                },
            }
        )

    base_scc = _compute_scc_signature(baseline)
    cand_scc = _compute_scc_signature(candidate)
    scc_match = (
        base_scc["component_count"] == cand_scc["component_count"]
        and base_scc["largest_component"] == cand_scc["largest_component"]
    )
    checks.append(
        {
            "name": "scc_signature",
            "pass": scc_match,
            "details": {"baseline": base_scc, "candidate": cand_scc},
        }
    )

    queries = _load_path_queries(query_file)
    path_rows: list[dict[str, Any]] = []
    path_matches = 0
    comparable = 0

    for q in queries:
        base_has = q.src in base_store.node_by_id and q.dst in base_store.node_by_id
        cand_has = q.src in cand_store.node_by_id and q.dst in cand_store.node_by_id
        if not (base_has and cand_has):
            path_rows.append(
                {
                    "from": q.src,
                    "to": q.dst,
                    "lawful_only": q.lawful_only,
                    "state_policy": q.state_policy,
                    "comparable": False,
                    "reason": "missing endpoint in one snapshot",
                }
            )
            continue

        comparable += 1
        base_path = base_store.shortest_path_with_state_policy(
            q.src, q.dst, lawful_only=q.lawful_only, state_policy=q.state_policy
        )
        cand_path = cand_store.shortest_path_with_state_policy(
            q.src, q.dst, lawful_only=q.lawful_only, state_policy=q.state_policy
        )

        base_found = bool(base_path.get("found"))
        cand_found = bool(cand_path.get("found"))
        base_len = len(base_path.get("path", []))
        cand_len = len(cand_path.get("path", []))

        matched = base_found == cand_found
        if matched and base_found and cand_found:
            matched = base_len == cand_len

        if matched:
            path_matches += 1

        path_rows.append(
            {
                "from": q.src,
                "to": q.dst,
                "lawful_only": q.lawful_only,
                "state_policy": q.state_policy,
                "comparable": True,
                "matched": matched,
                "baseline": {"found": base_found, "path_len": base_len},
                "candidate": {"found": cand_found, "path_len": cand_len},
            }
        )

    path_ratio = 1.0 if comparable == 0 else path_matches / comparable
    checks.append(
        {
            "name": "path_query_match",
            "pass": path_ratio >= min_path_match_ratio,
            "details": {
                "match_ratio": path_ratio,
                "min_required": min_path_match_ratio,
                "comparable": comparable,
                "matched": path_matches,
                "queries": path_rows,
            },
        }
    )

    required_locked_paths = _load_required_locked_paths(required_locked_paths_file)
    if required_locked_paths:
        lock_rows: list[dict[str, Any]] = []
        lock_ok = 0
        for q in required_locked_paths:
            has = q.src in cand_store.node_by_id and q.dst in cand_store.node_by_id
            if not has:
                lock_rows.append(
                    {
                        "from": q.src,
                        "to": q.dst,
                        "lawful_only": q.lawful_only,
                        "state_policy": q.state_policy,
                        "locked": False,
                        "reason": "missing endpoint in candidate snapshot",
                    }
                )
                continue
            path = cand_store.shortest_path_with_state_policy(
                q.src, q.dst, lawful_only=q.lawful_only, state_policy=q.state_policy
            )
            found = bool(path.get("found"))
            if found:
                lock_ok += 1
            lock_rows.append(
                {
                    "from": q.src,
                    "to": q.dst,
                    "lawful_only": q.lawful_only,
                    "state_policy": q.state_policy,
                    "locked": found,
                    "path_len": len(path.get("path", [])),
                }
            )
        checks.append(
            {
                "name": "required_path_locks",
                "pass": lock_ok == len(required_locked_paths),
                "details": {
                    "required": len(required_locked_paths),
                    "locked": lock_ok,
                    "rows": lock_rows,
                },
            }
        )

    base_coh = set(_top_ids(base_store.coherence_hotspots(limit=hotspot_limit), hotspot_limit))
    cand_coh = set(_top_ids(cand_store.coherence_hotspots(limit=hotspot_limit), hotspot_limit))
    coh_j = _jaccard(base_coh, cand_coh)
    checks.append(
        {
            "name": "coherence_hotspot_jaccard",
            "pass": coh_j >= min_coherence_jaccard,
            "details": {
                "jaccard": coh_j,
                "min_required": min_coherence_jaccard,
                "baseline_top": sorted(base_coh),
                "candidate_top": sorted(cand_coh),
            },
        }
    )

    base_hol = set(_top_ids(base_store.holonomy_hotspots(limit=hotspot_limit), hotspot_limit))
    cand_hol = set(_top_ids(cand_store.holonomy_hotspots(limit=hotspot_limit), hotspot_limit))
    hol_j = _jaccard(base_hol, cand_hol)
    checks.append(
        {
            "name": "holonomy_hotspot_jaccard",
            "pass": hol_j >= min_holonomy_jaccard,
            "details": {
                "jaccard": hol_j,
                "min_required": min_holonomy_jaccard,
                "baseline_top": sorted(base_hol),
                "candidate_top": sorted(cand_hol),
            },
        }
    )

    overall_pass = all(bool(row.get("pass", False)) for row in checks)

    return {
        "created_at": _utc_now(),
        "source": "tools.leantrail.conformance",
        "baseline": str(baseline_path),
        "baseline_format": baseline_format,
        "candidate": str(candidate_path),
        "candidate_format": candidate_format,
        "overall_pass": overall_pass,
        "checks": checks,
        "summary": {
            "check_count": len(checks),
            "failed_checks": [row.get("name") for row in checks if not bool(row.get("pass", False))],
            "node_drift_pct": node_drift,
            "edge_drift_pct": edge_drift,
            "path_match_ratio": path_ratio,
            "coherence_jaccard": coh_j,
            "holonomy_jaccard": hol_j,
            "baseline_metadata": baseline.metadata,
            "candidate_metadata": candidate.metadata,
        },
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Compare canonical LeanTrail snapshot against another snapshot or "
            "external analyzer export (GraphML / Neo4j CSV) and report "
            "conformance across counts, SCC signature, query paths, and "
            "hotspot overlap."
        )
    )
    parser.add_argument("--baseline", required=True, help="Baseline path")
    parser.add_argument(
        "--baseline-format",
        choices=_SNAPSHOT_FORMATS,
        default="snapshot",
        help="Baseline format.",
    )
    parser.add_argument("--candidate", required=True, help="Candidate path")
    parser.add_argument(
        "--candidate-format",
        choices=_SNAPSHOT_FORMATS,
        default="snapshot",
        help="Candidate format.",
    )
    parser.add_argument("--path-queries", default=None, help="Optional JSON file with path queries")
    parser.add_argument(
        "--required-locked-paths",
        default=None,
        help="Optional JSON file listing paths that must close under lock policy.",
    )
    parser.add_argument(
        "--json-out",
        default="artifacts/leantrail/conformance_report.json",
        help="Conformance report JSON output",
    )
    parser.add_argument(
        "--md-out",
        default="artifacts/leantrail/conformance_report.md",
        help="Conformance report Markdown output",
    )
    parser.add_argument("--hotspot-limit", type=int, default=25)
    parser.add_argument("--max-node-drift-pct", type=float, default=0.0)
    parser.add_argument("--max-edge-drift-pct", type=float, default=0.0)
    parser.add_argument("--min-path-match-ratio", type=float, default=1.0)
    parser.add_argument("--min-coherence-jaccard", type=float, default=0.9)
    parser.add_argument("--min-holonomy-jaccard", type=float, default=0.9)
    parser.add_argument("--require-same-toolchain", action="store_true")
    parser.add_argument(
        "--fail-on-violation",
        action="store_true",
        help="Exit non-zero if any check fails",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    baseline = Path(args.baseline).resolve()
    candidate = Path(args.candidate).resolve()
    baseline_format = str(args.baseline_format)
    candidate_format = str(args.candidate_format)
    query_file = Path(args.path_queries).resolve() if args.path_queries else None
    required_locked_paths_file = (
        Path(args.required_locked_paths).resolve() if args.required_locked_paths else None
    )
    json_out = Path(args.json_out).resolve()
    md_out = Path(args.md_out).resolve()

    if not baseline.exists():
        raise FileNotFoundError(f"Baseline path not found: {baseline}")
    if not candidate.exists():
        raise FileNotFoundError(f"Candidate path not found: {candidate}")
    if baseline_format in {"neo4j-csv", "arango-json"} and not baseline.is_dir():
        raise NotADirectoryError(f"Expected baseline directory for format '{baseline_format}': {baseline}")
    if candidate_format in {"neo4j-csv", "arango-json"} and not candidate.is_dir():
        raise NotADirectoryError(f"Expected candidate directory for format '{candidate_format}': {candidate}")
    if query_file is not None and not query_file.exists():
        raise FileNotFoundError(f"Path query file not found: {query_file}")
    if required_locked_paths_file is not None and not required_locked_paths_file.exists():
        raise FileNotFoundError(f"Required locked path file not found: {required_locked_paths_file}")

    report = run_conformance(
        baseline_path=baseline,
        baseline_format=baseline_format,
        candidate_path=candidate,
        candidate_format=candidate_format,
        query_file=query_file,
        required_locked_paths_file=required_locked_paths_file,
        hotspot_limit=args.hotspot_limit,
        max_node_drift_pct=args.max_node_drift_pct,
        max_edge_drift_pct=args.max_edge_drift_pct,
        min_path_match_ratio=args.min_path_match_ratio,
        min_coherence_jaccard=args.min_coherence_jaccard,
        min_holonomy_jaccard=args.min_holonomy_jaccard,
        require_same_toolchain=args.require_same_toolchain,
    )

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(_render_md(report), encoding="utf-8")

    print(f"LeanTrail conformance report written: {json_out}")
    print(f"LeanTrail conformance markdown written: {md_out}")
    print(f"Overall pass: {report['overall_pass']}")

    if args.fail_on_violation and not bool(report.get("overall_pass", False)):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
