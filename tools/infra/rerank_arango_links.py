#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.store import GraphStore
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.link_scorer_common import FeaturizerConfig, row_to_sparse_features, sigmoid, sparse_dot
from tools.leantrail.adapters import import_arango_json, load_snapshot


DEFAULT_MODEL = "reports/training/link_scorer_model.npz"
DEFAULT_OUT = "reports/training/arango_link_rerank.json"

_OBSTRUCTION_KINDS = {"obstructs", "violates_depth"}


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


def _safe_text(value: Any) -> str:
    if value is None:
        return ""
    return str(value).strip()


def _safe_int(value: Any, default: int | None = None) -> int | None:
    if isinstance(value, bool):
        return default
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        s = value.strip()
        if not s:
            return default
        try:
            return int(s)
        except Exception:
            return default
    return default


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                rows.append(row)
    return rows


def _load_model(path: Path) -> tuple[np.ndarray, float, FeaturizerConfig]:
    if not path.exists():
        raise FileNotFoundError(f"model not found: {path}")
    payload = np.load(path, allow_pickle=False)
    weights = payload["weights"].astype(np.float64)
    bias = float(payload["bias"][0])
    dim = int(payload["dim"][0])
    hash_seed = int(payload["hash_seed"][0])
    text_token_limit = int(payload["text_token_limit"][0])
    cfg = FeaturizerConfig(dim=dim, hash_seed=hash_seed, text_token_limit=text_token_limit)
    if weights.shape[0] != dim:
        raise RuntimeError(f"model mismatch: weights len={weights.shape[0]} dim={dim}")
    return weights, bias, cfg


def _snapshot_from_path(path: Path, fmt: str) -> GraphSnapshot:
    if fmt == "snapshot":
        return load_snapshot(path)
    if fmt == "arango-json":
        return import_arango_json(path)
    raise ValueError(f"unsupported input format: {fmt}")


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


def _fetch_arango_neighborhood(
    target: ArangoTarget,
    *,
    center: str,
    radius: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    query = """
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
  nodes: APPEND([start], nodes, true),
  edges: edges
}
""".strip()
    rows = _aql(
        target,
        query,
        {
            "@nodes": target.nodes_collection,
            "@edges": target.edges_collection,
            "center": center,
            "radius": int(radius),
        },
    )
    if not rows or not isinstance(rows[0], dict):
        return [], []
    block = rows[0]
    nodes = block.get("nodes", [])
    edges = block.get("edges", [])
    if not isinstance(nodes, list):
        nodes = []
    if not isinstance(edges, list):
        edges = []
    return [n for n in nodes if isinstance(n, dict)], [e for e in edges if isinstance(e, dict)]


def _read_file_snippet(file_path: str, line: int | None, *, radius: int, max_chars: int, cache: dict[str, list[str]]) -> str:
    if line is None:
        return ""
    p = Path(file_path)
    if not p.exists():
        return ""
    key = str(p)
    lines = cache.get(key)
    if lines is None:
        try:
            lines = p.read_text(encoding="utf-8", errors="ignore").splitlines()
        except Exception:
            lines = []
        cache[key] = lines
    if not lines:
        return ""
    idx = max(0, int(line) - 1)
    start = max(0, idx - max(0, radius))
    stop = min(len(lines), idx + max(0, radius) + 1)
    s = "\n".join(lines[start:stop]).strip()
    if not s:
        return ""
    if max_chars > 3 and len(s) > max_chars:
        s = s[: max_chars - 3] + "..."
    return s


def _decl_kind_of(node: dict[str, Any]) -> str:
    attrs = node.get("attrs")
    if isinstance(attrs, dict):
        dk = _safe_text(attrs.get("decl_kind"))
        if dk:
            return dk
    raw = _safe_text(node.get("kind")).lower()
    if raw == "declaration":
        return "declaration"
    return raw or "unknown"


def _to_decl_payload(node: dict[str, Any], *, snippet_radius: int, max_snippet_chars: int, cache: dict[str, list[str]]) -> dict[str, Any]:
    attrs = node.get("attrs")
    if not isinstance(attrs, dict):
        attrs = {}
    file_path = _safe_text(node.get("file"))
    line = _safe_int(node.get("line"), None)
    return {
        "name": _safe_text(node.get("id")) or _safe_text(node.get("name")),
        "kind": _decl_kind_of(node),
        "module": _safe_text(node.get("module")),
        "module_family": _safe_text(node.get("module_family")),
        "file": file_path,
        "line": line,
        "doc": _safe_text(attrs.get("doc")),
        "lean_snippet": _read_file_snippet(
            file_path,
            line,
            radius=snippet_radius,
            max_chars=max_snippet_chars,
            cache=cache,
        ),
        "rep_depth": node.get("rep_depth"),
        "rep_depth_nat": _safe_int(attrs.get("rep_depth_nat"), None),
    }


def _is_declaration_node(node: dict[str, Any]) -> bool:
    return _safe_text(node.get("kind")).strip().lower() == "declaration"


def _node_name(node: dict[str, Any]) -> str:
    return _safe_text(node.get("id")) or _safe_text(node.get("name"))


def _stable_id(*parts: str) -> str:
    base = "|".join(parts)
    return "cand_" + hashlib.sha1(base.encode("utf-8")).hexdigest()[:20]


def _build_candidates(
    *,
    center: str,
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    candidate_limit: int,
    declaration_only: bool,
    allowed_decl_kinds: set[str],
    snippet_radius: int,
    max_snippet_chars: int,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    node_map: dict[str, dict[str, Any]] = {}
    for n in nodes:
        nid = _node_name(n)
        if nid:
            node_map[nid] = n
    if center not in node_map:
        return [], {"found_center": False, "reason": f"center not in neighborhood: {center}"}

    out_deg: dict[str, int] = {}
    in_deg: dict[str, int] = {}
    failure_pressure: dict[str, int] = {}
    direct_edges_by_dst: dict[str, list[dict[str, Any]]] = {}

    for e in edges:
        src = _safe_text(e.get("src"))
        dst = _safe_text(e.get("dst"))
        kind = _safe_text(e.get("kind"))
        if not src or not dst:
            continue
        if kind == "contains":
            continue
        out_deg[src] = out_deg.get(src, 0) + 1
        in_deg[dst] = in_deg.get(dst, 0) + 1
        if kind in _OBSTRUCTION_KINDS:
            failure_pressure[src] = failure_pressure.get(src, 0) + 1
            failure_pressure[dst] = failure_pressure.get(dst, 0) + 1
        if src == center:
            direct_edges_by_dst.setdefault(dst, []).append(e)

    source_node = node_map[center]
    cache: dict[str, list[str]] = {}
    src_payload = _to_decl_payload(
        source_node,
        snippet_radius=snippet_radius,
        max_snippet_chars=max_snippet_chars,
        cache=cache,
    )

    rows: list[dict[str, Any]] = []
    for tgt_id, tgt_node in node_map.items():
        if tgt_id == center:
            continue
        if declaration_only and not _is_declaration_node(tgt_node):
            continue
        tgt_kind = _decl_kind_of(tgt_node)
        if allowed_decl_kinds and tgt_kind not in allowed_decl_kinds:
            continue

        direct_edges = direct_edges_by_dst.get(tgt_id, [])
        edge_kinds = [_safe_text(e.get("kind")) for e in direct_edges]
        link_kind = "type" if "depends_type" in edge_kinds else "value"
        pair_error_kinds = sorted([k for k in edge_kinds if k in _OBSTRUCTION_KINDS])

        tgt_payload = _to_decl_payload(
            tgt_node,
            snippet_radius=snippet_radius,
            max_snippet_chars=max_snippet_chars,
            cache=cache,
        )

        row = {
            "id": _stable_id(center, tgt_id, link_kind),
            "split": "inference",
            "label": 0,
            "sample_kind": "candidate",
            "link_kind": link_kind,
            "weight": 1.0,
            "unusual_score": 0.0,
            "source": src_payload,
            "target": tgt_payload,
            "graph_context": {
                "source_out_degree": int(out_deg.get(center, 0)),
                "target_in_degree": int(in_deg.get(tgt_id, 0)),
                "same_module": _safe_text(src_payload.get("module")) == _safe_text(tgt_payload.get("module")),
                "same_module_family": _safe_text(src_payload.get("module_family"))
                == _safe_text(tgt_payload.get("module_family")),
            },
            "failure_context": {
                "source_failure_pressure": int(failure_pressure.get(center, 0)),
                "target_failure_pressure": int(failure_pressure.get(tgt_id, 0)),
                "pair_failure_count": len(pair_error_kinds),
                "pair_error_kinds": pair_error_kinds,
            },
            "retrieval": {
                "direct_edge_kinds": edge_kinds,
                "has_direct_edge": bool(direct_edges),
            },
        }
        rows.append(row)
        if candidate_limit > 0 and len(rows) >= candidate_limit:
            break

    meta = {
        "found_center": True,
        "candidate_count_raw": len(rows),
        "node_count": len(node_map),
        "edge_count": len(edges),
    }
    return rows, meta


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(REPO_ROOT)
    ap = argparse.ArgumentParser(
        description=(
            "Retrieve Arango neighborhood candidates around a center declaration "
            "and rerank them with local link scorer."
        )
    )
    ap.add_argument("--mode", choices=["local", "arango-http"], default="local")
    ap.add_argument("--center", required=True)
    ap.add_argument("--radius", type=int, default=2)
    ap.add_argument("--candidate-limit", type=int, default=2500)
    ap.add_argument("--top-k", type=int, default=200)
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--rows-out", default=None, help="Optional JSONL with reranked rows.")

    ap.add_argument("--input", default="artifacts/leantrail/arango")
    ap.add_argument("--input-format", choices=["snapshot", "arango-json"], default="arango-json")
    ap.add_argument("--limit-nodes", type=int, default=2000)

    ap.add_argument("--endpoint", default=arango_endpoint())
    ap.add_argument("--database", default=arango_database())
    ap.add_argument("--username", default=arango_username())
    ap.add_argument("--password", default=arango_password())
    ap.add_argument("--nodes-collection", default="ig_nodes")
    ap.add_argument("--edges-collection", default="ig_edges")

    ap.set_defaults(declaration_only=True)
    ap.add_argument("--declaration-only", dest="declaration_only", action="store_true")
    ap.add_argument("--include-non-declarations", dest="declaration_only", action="store_false")
    ap.add_argument(
        "--decl-kind-filter",
        default="",
        help="Optional comma-separated decl kinds (e.g. theorem,axiom,lemma).",
    )
    ap.add_argument("--snippet-radius", type=int, default=2)
    ap.add_argument("--max-snippet-chars", type=int, default=260)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    model_path = Path(args.model).resolve()
    out_path = Path(args.out).resolve()
    rows_out_path = Path(args.rows_out).resolve() if args.rows_out else None

    weights, bias, feat_cfg = _load_model(model_path)

    nodes: list[dict[str, Any]]
    edges: list[dict[str, Any]]
    input_meta: dict[str, Any] = {}

    if args.mode == "local":
        snapshot = _snapshot_from_path(Path(args.input).resolve(), args.input_format)
        store = GraphStore(snapshot)
        neigh = store.neighborhood(
            center=args.center,
            radius=max(0, int(args.radius)),
            limit_nodes=max(1, int(args.limit_nodes)),
        )
        nodes = neigh.get("nodes", [])
        edges = neigh.get("edges", [])
        if not isinstance(nodes, list):
            nodes = []
        if not isinstance(edges, list):
            edges = []
        input_meta = {
            "mode": "local",
            "input": str(Path(args.input).resolve()),
            "input_format": args.input_format,
            "limit_nodes": int(args.limit_nodes),
        }
    else:
        target = ArangoTarget(
            endpoint=str(args.endpoint).rstrip("/"),
            database=str(args.database),
            username=str(args.username),
            password=str(args.password),
            nodes_collection=str(args.nodes_collection),
            edges_collection=str(args.edges_collection),
        )
        nodes, edges = _fetch_arango_neighborhood(
            target,
            center=args.center,
            radius=max(0, int(args.radius)),
        )
        input_meta = {
            "mode": "arango-http",
            "endpoint": target.endpoint,
            "database": target.database,
            "nodes_collection": target.nodes_collection,
            "edges_collection": target.edges_collection,
        }

    allowed_decl_kinds = {x.strip() for x in str(args.decl_kind_filter).split(",") if x.strip()}
    candidates, retrieve_meta = _build_candidates(
        center=args.center,
        nodes=nodes,
        edges=edges,
        candidate_limit=max(0, int(args.candidate_limit)),
        declaration_only=bool(args.declaration_only),
        allowed_decl_kinds=allowed_decl_kinds,
        snippet_radius=max(0, int(args.snippet_radius)),
        max_snippet_chars=max(0, int(args.max_snippet_chars)),
    )
    if not retrieve_meta.get("found_center", False):
        raise RuntimeError(retrieve_meta.get("reason", "center not found"))

    scored_rows: list[dict[str, Any]] = []
    for row in candidates:
        feats = row_to_sparse_features(row, feat_cfg)
        logit = float(bias + sparse_dot(weights, feats))
        score = float(sigmoid(logit))
        rr = dict(row)
        rr["scorer"] = {
            "model_path": str(model_path),
            "score": score,
            "logit": logit,
        }
        scored_rows.append(rr)

    scored_rows.sort(key=lambda r: float(r.get("scorer", {}).get("score", 0.0)), reverse=True)
    if int(args.top_k) > 0:
        scored_rows = scored_rows[: int(args.top_k)]
    for rank, row in enumerate(scored_rows, start=1):
        row.setdefault("scorer", {})
        row["scorer"]["rank"] = rank

    report = {
        "created_at": _utc_now(),
        "center": args.center,
        "radius": int(args.radius),
        "model": str(model_path),
        "feature_config": {
            "dim": feat_cfg.dim,
            "hash_seed": feat_cfg.hash_seed,
            "text_token_limit": feat_cfg.text_token_limit,
        },
        "input": input_meta,
        "retrieval": retrieve_meta,
        "params": {
            "candidate_limit": int(args.candidate_limit),
            "top_k": int(args.top_k),
            "declaration_only": bool(args.declaration_only),
            "decl_kind_filter": sorted(allowed_decl_kinds),
            "snippet_radius": int(args.snippet_radius),
            "max_snippet_chars": int(args.max_snippet_chars),
        },
        "counts": {
            "candidate_count": len(candidates),
            "scored_count": len(scored_rows),
        },
        "top_candidates": scored_rows,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    if rows_out_path is not None:
        rows_out_path.parent.mkdir(parents=True, exist_ok=True)
        with rows_out_path.open("w", encoding="utf-8") as handle:
            for row in scored_rows:
                handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    print(f"rerank report: {out_path}")
    if rows_out_path is not None:
        print(f"rerank rows:   {rows_out_path}")
    print(
        "counts: "
        f"nodes={retrieve_meta.get('node_count', 0)} "
        f"edges={retrieve_meta.get('edge_count', 0)} "
        f"candidates={len(candidates)} "
        f"scored={len(scored_rows)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
