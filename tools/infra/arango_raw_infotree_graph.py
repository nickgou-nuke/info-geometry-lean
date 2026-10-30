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
import re
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
from tools.infra.arango_raw_infotree_ingest import (
    ArangoTarget,
    ROW_FILES,
    context_edge_collections,
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

# Include every exported navigation edge, not only the original stage-2 subset.
EDGE_DEFINITIONS.extend(
    {"collection": f"raw_infotree_node_{edge}_edges",
     "from": ["raw_infotree_nodes"], "to": [f"raw_infotree_{rows}"]}
    for edge, rows in (("goal", "goal_states"), ("fvar", "fvar_lineage"),
                       ("argument", "tactic_arguments"), ("message", "messages"))
)


def graph_definitions(layout: str = "expanded", collection_map: dict[str, str] | None = None) -> list[dict[str, Any]]:
    allowed = context_edge_collections(layout)
    definitions = [d for d in EDGE_DEFINITIONS if d["collection"] in allowed]
    if layout == "shared":
        for kind in ("mctx", "lctx"):
            for edge, source, dest in (("ref_context", "refs", "contexts"),
                                       ("context_decl", "contexts", "decls")):
                definitions.append({"collection": f"raw_infotree_{kind}_{edge}_edges",
                    "from": [f"raw_infotree_{kind}_{source}"],
                    "to": [f"raw_infotree_{kind}_{dest}"]})
    if {d["collection"] for d in definitions} != set(allowed):
        raise ValueError("graph definition does not cover the selected edge layout")
    names = {d["collection"] for d in definitions} | {
        name for d in definitions for name in d["from"] + d["to"]}
    mapping = collection_map if collection_map is not None else {name: name for name in names}
    if names - mapping.keys():
        raise ValueError("generation collection map is incomplete")
    return [{"collection": mapping[d["collection"]],
             "from": [mapping[n] for n in d["from"]],
             "to": [mapping[n] for n in d["to"]]} for d in definitions]


def generation_graph_spec(receipt: dict[str, Any], generation_id: str) -> tuple[str, list[dict[str, Any]]]:
    if not re.fullmatch(r"[0-9a-f]{24}", generation_id):
        raise ValueError("generation ID must be 24 lowercase hexadecimal characters")
    if (receipt.get("_key") != generation_id or receipt.get("status") != "complete"
            or receipt.get("schema") != "info_geometry.raw_infotree_generation.v1"):
        raise ValueError("completed matching raw InfoTree generation receipt required")
    layout = receipt.get("contextLayout", "expanded")
    names = set(ROW_FILES) | set(context_edge_collections(layout))
    if layout == "shared":
        names |= {f"raw_infotree_{k}_contexts" for k in ("mctx", "lctx")}
    expected = {n: f"{n}_g_{generation_id}" for n in names}
    if receipt.get("collections") != expected:
        raise ValueError("generation collection map does not match its identity and layout")
    return layout, graph_definitions(layout, expected)


def definition_signature(definitions: list[dict[str, Any]]) -> list[tuple]:
    return sorted((d["collection"], tuple(sorted(d["from"])), tuple(sorted(d["to"])))
                  for d in definitions)


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


def create_graph(target: ArangoTarget, graph_name: str, *, replace: bool, definitions: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    definitions = graph_definitions() if definitions is None else definitions
    if replace and graph_exists(target, graph_name):
        drop_graph(target, graph_name)
    elif graph_exists(target, graph_name):
        payload = request_json(
            "GET",
            graph_url(target, graph_name),
            username=target.username,
            password=target.password,
        )
        graph = payload.get("graph", {}) if isinstance(payload, dict) else {}
        if (definition_signature(graph.get("edgeDefinitions", [])) != definition_signature(definitions)
                or graph.get("orphanCollections", [])):
            raise ValueError("existing named graph differs from requested layout; use a distinct graph name")
        return {"created": False, "graph": graph}

    payload = {
        "name": graph_name,
        "edgeDefinitions": definitions,
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


def named_graph_counts(target: ArangoTarget, definitions: list[dict[str, Any]] | None = None) -> dict[str, int]:
    definitions = graph_definitions() if definitions is None else definitions
    collections = sorted({d["collection"] for d in definitions} |
                         {n for d in definitions for n in d["from"] + d["to"]})
    return {collection: collection_count(target, collection) for collection in collections}


def networkx_probe(target: ArangoTarget, graph_name: str, *, use_gpu: bool, node_collection: str = "raw_infotree_nodes") -> GraphProbe:
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
            default_node_type=node_collection,
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
    parser.add_argument("--graph-name", default=None)
    parser.add_argument("--generation-id", help="Use a completed immutable raw InfoTree generation")
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
    layout = "expanded"
    definitions = graph_definitions()
    if args.generation_id:
        if args.replace:
            raise ValueError("immutable generation graphs cannot be replaced")
        if not re.fullmatch(r"[0-9a-f]{24}", args.generation_id):
            raise ValueError("invalid generation ID")
        receipt = request_json("GET", db_url(target, f"/_api/document/raw_infotree_generations/{args.generation_id}"),
                               username=target.username, password=target.password)
        layout, definitions = generation_graph_spec(receipt, args.generation_id)
    graph_name = args.graph_name or (f"{RAW_INFOTREE_GRAPH_NAME}_g_{args.generation_id}"
                                    if args.generation_id else RAW_INFOTREE_GRAPH_NAME)
    # Count first: missing collections must not be silently created by Gharial.
    counts = named_graph_counts(target, definitions)
    graph_result = create_graph(target, graph_name, replace=bool(args.replace), definitions=definitions)
    report: dict[str, Any] = {
        "schema": "info_geometry.raw_infotree_named_graph.v1",
        "database": target.database,
        "graph_name": graph_name,
        "generation_id": args.generation_id,
        "context_layout": layout,
        "graph_created": graph_result["created"],
        "vertex_collections": sorted({n for d in definitions for n in d["from"] + d["to"]}),
        "edge_definitions": definitions,
        "counts": counts,
    }
    if args.probe_networkx:
        probe = networkx_probe(target, graph_name, use_gpu=bool(args.use_gpu),
            node_collection=f"raw_infotree_nodes_g_{args.generation_id}" if args.generation_id else "raw_infotree_nodes")
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
    print(f"Graph: {graph_name} created={graph_result['created']}")
    print("Counts: " + " ".join(f"{name}={count}" for name, count in report["counts"].items()))
    if "networkx_probe" in report:
        print("NetworkX probe: " + json.dumps(report["networkx_probe"], ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
