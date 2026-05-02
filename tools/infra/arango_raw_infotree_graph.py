#!/usr/bin/env python3
"""Create/probe a named ArangoDB graph for raw_infotree_* collections.

This is the handoff point from loss-audited compiler-memory rows to graph
analytics tooling. The named graph is an overlay over already imported
collections; it does not rewrite or summarize the raw rows.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from arango_raw_infotree_ingest import (
    ArangoTarget,
    auth_header,
    collection_count,
    db_url,
    request_json,
)


RAW_INFOTREE_GRAPH_NAME = "raw_infotree_stage2"

EDGE_DEFINITIONS: list[dict[str, Any]] = [
    {
        "collection": "raw_infotree_tree_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_nodes"],
    },
    {
        "collection": "raw_infotree_root_node_edges",
        "from": ["raw_infotree_roots"],
        "to": ["raw_infotree_nodes"],
    },
    {
        "collection": "raw_infotree_node_context_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_contexts"],
    },
    {
        "collection": "raw_infotree_node_payload_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_payloads"],
    },
    {
        "collection": "raw_infotree_payload_field_edges",
        "from": ["raw_infotree_payloads"],
        "to": ["raw_infotree_payload_fields"],
    },
    {
        "collection": "raw_infotree_node_decl_link_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_decl_links"],
    },
    {
        "collection": "raw_infotree_node_env_ref_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_env_refs"],
    },
    {
        "collection": "raw_infotree_node_mctx_ref_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_mctx_refs"],
    },
    {
        "collection": "raw_infotree_mctx_decl_edges",
        "from": ["raw_infotree_mctx_refs"],
        "to": ["raw_infotree_mctx_decls"],
    },
    {
        "collection": "raw_infotree_source_lctx_ref_edges",
        "from": ["raw_infotree_nodes", "raw_infotree_mctx_decls"],
        "to": ["raw_infotree_lctx_refs"],
    },
    {
        "collection": "raw_infotree_lctx_ref_decl_edges",
        "from": ["raw_infotree_lctx_refs"],
        "to": ["raw_infotree_lctx_decls"],
    },
    {
        "collection": "raw_infotree_node_leakage_edges",
        "from": ["raw_infotree_nodes"],
        "to": ["raw_infotree_projection_leakage"],
    },
]

VERTEX_COLLECTIONS = sorted(
    {
        col
        for definition in EDGE_DEFINITIONS
        for endpoint in (definition["from"] + definition["to"])
        for col in [endpoint]
    }
)


@dataclass(frozen=True)
class GraphProbe:
    available: bool
    node_count: int | None = None
    edge_count: int | None = None
    gpu_backend_requested: bool = False
    backend_priority_algos: list[str] | None = None
    backend_priority_generators: list[str] | None = None
    error: str | None = None


def graph_url(target: ArangoTarget, graph_name: str = "") -> str:
    suffix = f"/{quote(graph_name)}" if graph_name else ""
    return db_url(target, f"/_api/gharial{suffix}")


def graph_exists(target: ArangoTarget, graph_name: str) -> bool:
    try:
        payload = request_json(
            "GET",
            graph_url(target, graph_name),
            username=target.username,
            password=target.password,
        )
        return isinstance(payload, dict) and not payload.get("error", False)
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


def create_graph(target: ArangoTarget, graph_name: str, *, replace: bool) -> dict[str, Any]:
    if replace and graph_exists(target, graph_name):
        drop_graph(target, graph_name)
    elif graph_exists(target, graph_name):
        payload = request_json(
            "GET",
            graph_url(target, graph_name),
            username=target.username,
            password=target.password,
        )
        return {"created": False, "graph": payload.get("graph") if isinstance(payload, dict) else payload}

    payload = {
        "name": graph_name,
        "edgeDefinitions": EDGE_DEFINITIONS,
        "orphanCollections": [],
        "isSmart": False,
    }
    result = request_json(
        "POST",
        graph_url(target),
        username=target.username,
        password=target.password,
        payload=payload,
    )
    return {"created": True, "graph": result.get("graph") if isinstance(result, dict) else result}


def named_graph_counts(target: ArangoTarget) -> dict[str, int]:
    collections = VERTEX_COLLECTIONS + [definition["collection"] for definition in EDGE_DEFINITIONS]
    return {collection: collection_count(target, collection) for collection in collections}


def networkx_probe(target: ArangoTarget, graph_name: str, *, use_gpu: bool) -> GraphProbe:
    if use_gpu:
        # Do not use NX_CUGRAPH_AUTOCONFIG here. RAPIDS 26.04 sets
        # NETWORKX_BACKEND_PRIORITY_CLASSES, which NetworkX 3.5 rejects while
        # nx-arangodb 1.3.1 still pins NetworkX <= 3.5. These native NetworkX
        # backend variables enable cuGraph dispatch without violating that pin.
        os.environ.setdefault("NETWORKX_BACKEND_PRIORITY_ALGOS", "cugraph")
        os.environ.setdefault("NETWORKX_BACKEND_PRIORITY_GENERATORS", "cugraph")
        os.environ.setdefault("NETWORKX_FALLBACK_TO_NX", "true")
        os.environ.setdefault("NETWORKX_CACHE_CONVERTED_GRAPHS", "true")

    try:
        import networkx as nx  # type: ignore
        from arango import ArangoClient  # type: ignore
        import nx_arangodb as nxadb  # type: ignore
    except Exception as exc:
        return GraphProbe(available=False, gpu_backend_requested=use_gpu, error=f"missing dependency: {exc}")

    try:
        if hasattr(nx, "config") and hasattr(nx.config, "backends"):
            try:
                nx.config.backends.arangodb.use_gpu = bool(use_gpu)
            except Exception:
                pass
        algos = list(getattr(getattr(nx.config, "backend_priority", object()), "algos", []))
        generators = list(getattr(getattr(nx.config, "backend_priority", object()), "generators", []))

        # Pass the database object directly. nx-arangodb's environment-variable
        # connector treats an empty password as "not set", but local development
        # Arango instances can legitimately run with an empty root password.
        db = ArangoClient(hosts=target.endpoint, request_timeout=None).db(
            target.database,
            username=target.username,
            password=target.password,
            verify=True,
        )
        graph = nxadb.DiGraph(
            name=graph_name,
            db=db,
            default_node_type="raw_infotree_nodes",
        )
        return GraphProbe(
            available=True,
            node_count=graph.number_of_nodes(),
            edge_count=graph.number_of_edges(),
            gpu_backend_requested=use_gpu,
            backend_priority_algos=algos,
            backend_priority_generators=generators,
        )
    except Exception as exc:
        return GraphProbe(available=False, gpu_backend_requested=use_gpu, error=str(exc))


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(REPO_ROOT)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    parser.add_argument("--graph-name", default=RAW_INFOTREE_GRAPH_NAME)
    parser.add_argument("--replace", action="store_true", help="Replace the named graph definition without dropping collections.")
    parser.add_argument("--probe-networkx", action="store_true", help="Try opening the graph through nx-arangodb if installed.")
    parser.add_argument("--use-gpu", action="store_true", help="Request nx-cugraph dispatch when probing through nx-arangodb.")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/infotree/raw_infotree_named_graph_report.json"))
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = ArangoTarget(
        endpoint=str(args.endpoint).rstrip("/"),
        database=str(args.database),
        username=str(args.username),
        password=str(args.password),
    )
    graph_result = create_graph(target, str(args.graph_name), replace=bool(args.replace))
    report: dict[str, Any] = {
        "schema": "info_geometry.raw_infotree_named_graph.v1",
        "database": target.database,
        "graph_name": str(args.graph_name),
        "graph_created": graph_result["created"],
        "vertex_collections": VERTEX_COLLECTIONS,
        "edge_definitions": EDGE_DEFINITIONS,
        "counts": named_graph_counts(target),
    }
    if args.probe_networkx:
        probe = networkx_probe(target, str(args.graph_name), use_gpu=bool(args.use_gpu))
        report["networkx_probe"] = {
            "available": probe.available,
            "node_count": probe.node_count,
            "edge_count": probe.edge_count,
            "gpu_backend_requested": probe.gpu_backend_requested,
            "backend_priority_algos": probe.backend_priority_algos,
            "backend_priority_generators": probe.backend_priority_generators,
            "error": probe.error,
        }

    out_path = args.json_out.resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"Raw InfoTree named graph report written: {out_path}")
    print(f"Graph: {args.graph_name} created={graph_result['created']}")
    print("Counts: " + " ".join(f"{name}={count}" for name, count in report["counts"].items()))
    if "networkx_probe" in report:
        print("NetworkX probe: " + json.dumps(report["networkx_probe"], ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
