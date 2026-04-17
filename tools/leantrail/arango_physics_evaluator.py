#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.store import GraphStore
from tools.leantrail.adapters import import_arango_json, load_snapshot


_DEP_KINDS = {"depends_type", "depends_value"}
_OBSTRUCTION_KINDS = {"obstructs", "violates_depth"}
_COHERENCE_KINDS = {"coheres_with", "translator_of"}


@dataclass(frozen=True)
class PhysicsWeights:
    alpha: float
    beta: float
    gamma: float


@dataclass(frozen=True)
class ArangoTarget:
    endpoint: str
    database: str
    username: str
    password: str
    nodes_collection: str
    edges_collection: str


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _safe_float(value: Any, default: float = 0.0) -> float:
    if isinstance(value, bool):
        return default
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        s = value.strip()
        if not s:
            return default
        try:
            return float(s)
        except Exception:
            return default
    return default


def _snapshot_from_path(path: Path, fmt: str) -> GraphSnapshot:
    if fmt == "snapshot":
        return load_snapshot(path)
    if fmt == "arango-json":
        return import_arango_json(path)
    raise ValueError(f"Unsupported snapshot format: {fmt}")


def _local_eval(
    snapshot: GraphSnapshot,
    *,
    center: str,
    radius: int,
    weights: PhysicsWeights,
    target: str | None,
    lawful_only: bool,
    path_state_policy: str,
) -> dict[str, Any]:
    store = GraphStore(snapshot)
    neighborhood = store.neighborhood(center=center, radius=radius)
    nodes = neighborhood.get("nodes", [])
    edges = neighborhood.get("edges", [])
    if not isinstance(nodes, list):
        nodes = []
    if not isinstance(edges, list):
        edges = []

    metrics = _compute_metrics(nodes=nodes, edges=edges, weights=weights)
    metrics["center"] = center
    metrics["radius"] = radius

    if target:
        path_payload = store.shortest_path_with_state_policy(
            center,
            target,
            lawful_only=lawful_only,
            state_policy=path_state_policy,
        )
        path_edges = path_payload.get("edges", [])
        if not isinstance(path_edges, list):
            path_edges = []
        path_metrics = _compute_metrics(nodes=[], edges=path_edges, weights=weights)
        metrics["path"] = {
            "target": target,
            "found": bool(path_payload.get("found", False)),
            "node_path": path_payload.get("path", []),
            "state_policy": path_state_policy,
            "edge_count": len(path_edges),
            "surprisal": path_metrics["surprisal"],
            "action_sum": path_metrics["action_sum"],
            "obstruction_count": path_metrics["obstruction_count"],
            "coherence_count": path_metrics["coherence_count"],
        }

    return metrics


def _auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def _db_url(target: ArangoTarget, path: str) -> str:
    return f"{target.endpoint}/_db/{quote(target.database)}/{path.lstrip('/')}"


def _request_json(
    method: str,
    url: str,
    *,
    username: str,
    password: str,
    payload: dict[str, Any] | None = None,
) -> dict[str, Any]:
    body = json.dumps(payload, ensure_ascii=True).encode("utf-8") if payload is not None else None
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", _auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")

    try:
        with urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc


def _aql(target: ArangoTarget, query: str, bind_vars: dict[str, Any]) -> list[Any]:
    out = _request_json(
        "POST",
        _db_url(target, "/_api/cursor"),
        username=target.username,
        password=target.password,
        payload={"query": query, "bindVars": bind_vars},
    )
    rows = out.get("result")
    if isinstance(rows, list):
        return rows
    return []


def _arango_eval(
    target: ArangoTarget,
    *,
    center: str,
    radius: int,
    weights: PhysicsWeights,
    target_node: str | None,
) -> dict[str, Any]:
    neighborhood_query = """
LET start = FIRST(
  FOR n IN @@nodes
    FILTER n.id == @center
    LIMIT 1
    RETURN n
)
FILTER start != null
LET nodes = (
  FOR v, e, p IN 1..@radius ANY start @@edges
    OPTIONS { bfs: true, uniqueVertices: "global" }
    RETURN DISTINCT v
)
LET edges = (
  FOR v, e, p IN 1..@radius ANY start @@edges
    OPTIONS { bfs: true, uniqueVertices: "global" }
    FOR pe IN p.edges
      RETURN DISTINCT pe
)
RETURN {
  start: start,
  nodes: APPEND([start], nodes, true),
  edges: edges
}
""".strip()

    rows = _aql(
        target,
        neighborhood_query,
        {
            "@nodes": target.nodes_collection,
            "@edges": target.edges_collection,
            "center": center,
            "radius": int(radius),
        },
    )

    if not rows:
        return {
            "center": center,
            "radius": radius,
            "node_count": 0,
            "edge_count": 0,
            "action_sum": 0.0,
            "dependency_count": 0,
            "obstruction_count": 0,
            "coherence_count": 0,
            "surprisal": 0.0,
            "thermal_efficiency": 1.0,
            "mode": "arango-http",
            "found": False,
        }

    block = rows[0] if isinstance(rows[0], dict) else {}
    nodes = block.get("nodes", [])
    edges = block.get("edges", [])
    if not isinstance(nodes, list):
        nodes = []
    if not isinstance(edges, list):
        edges = []

    metrics = _compute_metrics(nodes=nodes, edges=edges, weights=weights)
    metrics["center"] = center
    metrics["radius"] = radius
    metrics["mode"] = "arango-http"
    metrics["found"] = True

    if target_node:
        path_query = """
LET src = FIRST(
  FOR n IN @@nodes
    FILTER n.id == @src
    LIMIT 1
    RETURN n
)
LET dst = FIRST(
  FOR n IN @@nodes
    FILTER n.id == @dst
    LIMIT 1
    RETURN n
)
FILTER src != null && dst != null
LET p = FIRST(
  FOR v, e, p IN ANY SHORTEST_PATH src TO dst @@edges
    RETURN p
)
RETURN p
""".strip()
        p_rows = _aql(
            target,
            path_query,
            {
                "@nodes": target.nodes_collection,
                "@edges": target.edges_collection,
                "src": center,
                "dst": target_node,
            },
        )
        path = p_rows[0] if p_rows and isinstance(p_rows[0], dict) else {}
        path_edges = path.get("edges", [])
        path_vertices = path.get("vertices", [])
        if not isinstance(path_edges, list):
            path_edges = []
        if not isinstance(path_vertices, list):
            path_vertices = []

        path_metrics = _compute_metrics(nodes=[], edges=path_edges, weights=weights)
        metrics["path"] = {
            "target": target_node,
            "found": bool(path),
            "node_path": [v.get("id", "") for v in path_vertices if isinstance(v, dict)],
            "edge_count": len(path_edges),
            "surprisal": path_metrics["surprisal"],
            "action_sum": path_metrics["action_sum"],
            "obstruction_count": path_metrics["obstruction_count"],
            "coherence_count": path_metrics["coherence_count"],
        }

    return metrics


def _compute_metrics(
    *,
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    weights: PhysicsWeights,
) -> dict[str, Any]:
    edge_count = len(edges)
    node_count = len(nodes)
    action_sum = sum(_safe_float(edge.get("weight"), 1.0) for edge in edges)

    dep_count = 0
    obstruction_count = 0
    coherence_count = 0
    for edge in edges:
        kind = str(edge.get("kind", "")).strip()
        if kind in _DEP_KINDS:
            dep_count += 1
        if kind in _OBSTRUCTION_KINDS:
            obstruction_count += 1
        if kind in _COHERENCE_KINDS:
            coherence_count += 1

    surprisal_raw = (
        weights.alpha * action_sum
        + weights.beta * float(obstruction_count)
        - weights.gamma * float(coherence_count)
    )
    surprisal = max(0.0, float(surprisal_raw))
    thermal_efficiency = 1.0 / (1.0 + surprisal)

    return {
        "node_count": node_count,
        "edge_count": edge_count,
        "action_sum": action_sum,
        "dependency_count": dep_count,
        "obstruction_count": obstruction_count,
        "coherence_count": coherence_count,
        "surprisal": surprisal,
        "thermal_efficiency": thermal_efficiency,
        "weights": {
            "alpha": weights.alpha,
            "beta": weights.beta,
            "gamma": weights.gamma,
        },
    }


def _render_md(report: dict[str, Any]) -> str:
    lines = [
        "# LeanTrail Arango Physics Evaluation",
        "",
        f"- Created: `{report.get('created_at', '')}`",
        f"- Mode: `{report.get('mode', '')}`",
        "",
    ]

    if "evaluation" in report:
        eval_row = report["evaluation"]
        lines.extend(
            [
                "## Evaluation",
                "",
                f"- center: `{eval_row.get('center', '')}`",
                f"- radius: `{eval_row.get('radius', '')}`",
                f"- node_count: `{eval_row.get('node_count', 0)}`",
                f"- edge_count: `{eval_row.get('edge_count', 0)}`",
                f"- action_sum: `{eval_row.get('action_sum', 0.0)}`",
                f"- surprisal: `{eval_row.get('surprisal', 0.0)}`",
                f"- thermal_efficiency: `{eval_row.get('thermal_efficiency', 0.0)}`",
                "",
            ]
        )

    if "baseline" in report and "candidate" in report:
        base = report["baseline"]
        cand = report["candidate"]
        delta = report.get("delta", {})
        lines.extend(
            [
                "## Baseline vs Candidate",
                "",
                f"- center: `{report.get('center', '')}`",
                f"- baseline_surprisal: `{base.get('surprisal', 0.0)}`",
                f"- candidate_surprisal: `{cand.get('surprisal', 0.0)}`",
                f"- delta_surprisal: `{delta.get('delta_surprisal', 0.0)}`",
                f"- improved: `{delta.get('improved', False)}`",
                "",
            ]
        )

    lines.extend(["## Raw", "", "```json", json.dumps(report, indent=2, ensure_ascii=True), "```"])
    return "\n".join(lines) + "\n"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Evaluate local or ArangoDB LeanTrail neighborhoods as a physical "
            "surprisal surface, with optional baseline/candidate delta."
        )
    )
    parser.add_argument("--mode", choices=["local", "arango-http"], default="local")
    parser.add_argument("--center", required=True)
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--target", default=None)
    parser.add_argument("--lawful-only", action="store_true")
    parser.add_argument(
        "--path-state-policy",
        choices=["any", "exclude-failed", "locked-only"],
        default="exclude-failed",
        help="Traversal policy used when target path metrics are requested in local mode.",
    )

    parser.add_argument("--alpha", type=float, default=1.0)
    parser.add_argument("--beta", type=float, default=2.0)
    parser.add_argument("--gamma", type=float, default=1.0)

    parser.add_argument("--input", default="artifacts/leantrail/arango")
    parser.add_argument("--input-format", choices=["snapshot", "arango-json"], default="arango-json")
    parser.add_argument("--candidate-input", default=None)
    parser.add_argument(
        "--candidate-format", choices=["snapshot", "arango-json"], default="arango-json"
    )

    parser.add_argument("--endpoint", default="http://127.0.0.1:8529")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--username", default="root")
    parser.add_argument("--password", default="")
    parser.add_argument("--nodes-collection", default="ig_nodes")
    parser.add_argument("--edges-collection", default="ig_edges")

    parser.add_argument(
        "--json-out",
        default="artifacts/leantrail/arango_physics_report.json",
        help="Write report JSON here.",
    )
    parser.add_argument(
        "--md-out",
        default=None,
        help="Optional markdown report path.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    weights = PhysicsWeights(alpha=float(args.alpha), beta=float(args.beta), gamma=float(args.gamma))

    report: dict[str, Any] = {
        "created_at": _utc_now(),
        "mode": args.mode,
        "center": args.center,
        "radius": int(args.radius),
        "weights": {"alpha": weights.alpha, "beta": weights.beta, "gamma": weights.gamma},
    }

    if args.mode == "local":
        baseline = _snapshot_from_path(Path(args.input).resolve(), args.input_format)
        baseline_eval = _local_eval(
            baseline,
            center=args.center,
            radius=int(args.radius),
            weights=weights,
            target=args.target,
            lawful_only=bool(args.lawful_only),
            path_state_policy=str(args.path_state_policy),
        )

        if args.candidate_input:
            candidate = _snapshot_from_path(Path(args.candidate_input).resolve(), args.candidate_format)
            candidate_eval = _local_eval(
                candidate,
                center=args.center,
                radius=int(args.radius),
                weights=weights,
                target=args.target,
                lawful_only=bool(args.lawful_only),
                path_state_policy=str(args.path_state_policy),
            )
            delta_surprisal = float(candidate_eval["surprisal"]) - float(baseline_eval["surprisal"])
            delta_eff = float(candidate_eval["thermal_efficiency"]) - float(
                baseline_eval["thermal_efficiency"]
            )
            report["baseline"] = baseline_eval
            report["candidate"] = candidate_eval
            report["delta"] = {
                "delta_surprisal": delta_surprisal,
                "delta_efficiency": delta_eff,
                "improved": delta_surprisal < 0.0,
            }
        else:
            report["evaluation"] = baseline_eval

    else:
        if args.candidate_input:
            raise ValueError("candidate compare mode is supported only with --mode local")
        target = ArangoTarget(
            endpoint=str(args.endpoint).rstrip("/"),
            database=str(args.database),
            username=str(args.username),
            password=str(args.password),
            nodes_collection=str(args.nodes_collection),
            edges_collection=str(args.edges_collection),
        )
        report["evaluation"] = _arango_eval(
            target,
            center=args.center,
            radius=int(args.radius),
            weights=weights,
            target_node=args.target,
        )
        report["arango"] = {
            "endpoint": target.endpoint,
            "database": target.database,
            "nodes_collection": target.nodes_collection,
            "edges_collection": target.edges_collection,
        }

    json_out = Path(args.json_out).resolve()
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"Physics report written: {json_out}")

    if args.md_out:
        md_out = Path(args.md_out).resolve()
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(_render_md(report), encoding="utf-8")
        print(f"Physics markdown report written: {md_out}")

    if "delta" in report:
        delta = report["delta"]
        print(
            "Delta: surprisal="
            f"{delta.get('delta_surprisal', 0.0):.6f}, "
            f"efficiency={delta.get('delta_efficiency', 0.0):.6f}, "
            f"improved={delta.get('improved', False)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
