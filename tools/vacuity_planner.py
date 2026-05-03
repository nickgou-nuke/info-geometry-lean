#!/usr/bin/env python3
"""Planning-only vacuity planner orchestrator.

This tool aggregates read-only compiler bridge payloads, vacuity reports,
dependency metadata, and ownership metadata to produce ranked planning outputs:

- ranked vacuity candidates
- ranked owner candidates
- ranked replacement candidates

Boundary:
- no mutation surface
- no automatic replacement
- no proof repair
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import cast

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.pathing import normalize_user_path, repo_root
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.planner.admissibility import rank_admissibility_prechecks
from tools.planner.common import (
    DIAG_PROVENANCE_WEIGHT,
    HEAD_SOURCE_WEIGHT,
    VIOLATION_LEVEL_WEIGHT,
    JsonObj,
    load_decl_index,
    load_edges,
    load_json,
    load_module_regions,
    load_owner_index,
    load_proof_hole_counts,
    relpath_or_self,
    resolve_existing,
)
from tools.planner.matching import build_decl_match_context
from tools.planner.normalization import (
    collect_bridge_json_paths,
    extract_bridge_payload_objects,
    normalize_bridge_observations,
    observe_bridge_payload,
)
from tools.planner.policy import planner_policy_snapshot
from tools.planner.ranking import (
    rank_declaration_plans,
    rank_fingerprint_corridors,
    rank_owner_candidates,
    rank_replacement_candidates,
    rank_vacuity_candidates,
)
from tools.planner.report import make_markdown_report


def parse_args() -> argparse.Namespace:
    root = repo_root()
    load_repo_arango_env(root)

    parser = argparse.ArgumentParser(description="Planning-only vacuity planner orchestrator")
    parser.add_argument(
        "--graph-source",
        choices=["auto", "artifacts", "arango"],
        default="artifacts",
        help=(
            "Source for declaration and dependency graph metadata. "
            "`artifacts` preserves the original JSONL behavior; `arango` "
            "loads live graph collections; `auto` tries Arango then falls back."
        ),
    )
    parser.add_argument("--bridge-input", action="append", default=[], help="JSON file/dir/glob with bridge payload data")
    parser.add_argument(
        "--theorem-significance",
        type=Path,
        default=root / "reports" / "theorem-significance.json",
        help="JSON report from tools/theorem_significance.py",
    )
    parser.add_argument(
        "--decls",
        type=Path,
        default=resolve_existing(
            root / "index" / "decls.jsonl",
            root / "artifacts" / "dag" / "index" / "decls.jsonl",
            root / ".build" / "index" / "decls.jsonl",
        )
        or (root / "index" / "decls.jsonl"),
        help="Declaration metadata JSONL",
    )
    parser.add_argument(
        "--edges",
        type=Path,
        default=resolve_existing(
            root / "index" / "edges.jsonl",
            root / "artifacts" / "dag" / "index" / "edges.jsonl",
            root / ".build" / "index" / "edges.jsonl",
        )
        or (root / "index" / "edges.jsonl"),
        help="Dependency edge metadata JSONL",
    )
    parser.add_argument("--arango-url", default=arango_endpoint())
    parser.add_argument("--arango-db", default=arango_database())
    parser.add_argument("--arango-user", default=arango_username())
    parser.add_argument("--arango-password", default=arango_password())
    parser.add_argument("--arango-nodes-collection", default="ig_nodes")
    parser.add_argument("--arango-edges-collection", default="ig_edges")
    parser.add_argument("--arango-limit-nodes", type=int, default=200000)
    parser.add_argument("--arango-limit-edges", type=int, default=500000)
    parser.add_argument(
        "--module-graph",
        type=Path,
        default=root / "docs-map" / "module_graph.json",
        help="Module graph JSON",
    )
    parser.add_argument(
        "--owner-index",
        type=Path,
        default=root / "reports" / "dag" / "representation-depth-index.json",
        help="Ownership index JSON",
    )
    parser.add_argument(
        "--proof-holes-by-file",
        type=Path,
        default=root / "reports" / "vacuity" / "wholecode-explicit-proof-holes-20260309.by-file.txt",
        help="Optional proof-hole count by file",
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=root / "reports" / "vacuity-planner.json",
        help="Planner JSON output",
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=root / "reports" / "vacuity-planner.md",
        help="Planner Markdown output",
    )
    parser.add_argument("--top-k", type=int, default=50, help="Maximum rows per ranked output")
    return parser.parse_args()


def _load_graph_from_arango(args: argparse.Namespace) -> tuple[dict[str, JsonObj], dict[str, list[tuple[str, str]]]]:
    root = repo_root()
    src_root = root / "src"
    if str(src_root) not in sys.path:
        sys.path.insert(0, str(src_root))

    from igf.graph import ArangoHttpTarget, execute_aql

    target = ArangoHttpTarget(
        endpoint=str(args.arango_url).rstrip("/"),
        database=str(args.arango_db),
        username=str(args.arango_user),
        password=str(args.arango_password),
    )
    node_rows = execute_aql(
        target,
        """
        FOR n IN @@nodes
          LIMIT @limit
          RETURN {
            name: n.name,
            kind: n.kind,
            module: n.module,
            file: n.file,
            line: n.line,
            column: n.column,
            doc: n.doc,
            attrs: n.attrs,
            typeFingerprint: n.typeFingerprint,
            valueFingerprint: n.valueFingerprint
          }
        """,
        {"@nodes": str(args.arango_nodes_collection), "limit": int(args.arango_limit_nodes)},
        timeout=60,
    )
    edge_rows = execute_aql(
        target,
        """
        FOR e IN @@edges
          LIMIT @limit
          RETURN {
            src: e.src != null ? e.src : PARSE_IDENTIFIER(e._from).key,
            dst: e.dst != null ? e.dst : PARSE_IDENTIFIER(e._to).key,
            kind: e.kind != null ? e.kind : "value"
          }
        """,
        {"@edges": str(args.arango_edges_collection), "limit": int(args.arango_limit_edges)},
        timeout=60,
    )

    decls: dict[str, JsonObj] = {}
    for row in node_rows:
        if not isinstance(row, dict):
            continue
        name = row.get("name")
        if not name:
            continue
        decls[str(name)] = cast(JsonObj, row)

    forward: dict[str, list[tuple[str, str]]] = {}
    for row in edge_rows:
        if not isinstance(row, dict):
            continue
        src = row.get("src")
        dst = row.get("dst")
        if not src or not dst:
            continue
        forward.setdefault(str(src), []).append((str(dst), str(row.get("kind") or "value")))
    return decls, forward


def _load_graph_inputs(
    args: argparse.Namespace, decls_path: Path, edges_path: Path
) -> tuple[str, dict[str, JsonObj], dict[str, list[tuple[str, str]]]]:
    if args.graph_source in {"auto", "arango"}:
        try:
            decls, forward_edges = _load_graph_from_arango(args)
            if decls:
                return "arango", decls, forward_edges
            if args.graph_source == "arango":
                raise RuntimeError("Arango graph source returned no declarations")
        except Exception:
            if args.graph_source == "arango":
                raise

    forward_edges, _ = load_edges(edges_path)
    return "artifacts", load_decl_index(decls_path), forward_edges


def main() -> None:
    root = repo_root()
    args = parse_args()

    theorem_significance_path = normalize_user_path(str(args.theorem_significance), args.theorem_significance)
    decls_path = normalize_user_path(str(args.decls), args.decls)
    edges_path = normalize_user_path(str(args.edges), args.edges)
    module_graph_path = normalize_user_path(str(args.module_graph), args.module_graph)
    owner_index_path = normalize_user_path(str(args.owner_index), args.owner_index)
    proof_holes_path = normalize_user_path(str(args.proof_holes_by_file), args.proof_holes_by_file)
    out_json_path = normalize_user_path(str(args.out_json), args.out_json)
    out_md_path = normalize_user_path(str(args.out_md), args.out_md)

    theorem_entries_raw = load_json(theorem_significance_path)
    if not isinstance(theorem_entries_raw, list):
        raise RuntimeError(f"Expected list in theorem significance report: {theorem_significance_path}")
    theorem_entries: list[JsonObj] = [cast(JsonObj, row) for row in theorem_entries_raw if isinstance(row, dict)]

    graph_source_used, decls, forward_edges = _load_graph_inputs(args, decls_path, edges_path)
    module_region, file_region = load_module_regions(module_graph_path, root)
    owner_entries = load_owner_index(owner_index_path)

    hole_counts: dict[str, int] = {}
    if proof_holes_path.exists():
        hole_counts = load_proof_hole_counts(proof_holes_path)

    decl_match_ctx = build_decl_match_context(theorem_entries, decls, root)

    bridge_json_paths = collect_bridge_json_paths(args.bridge_input, root)
    bridge_payload_count = 0
    observations: list[JsonObj] = []
    for p in bridge_json_paths:
        try:
            parsed = load_json(p)
        except Exception:
            continue
        payloads = extract_bridge_payload_objects(parsed)
        bridge_payload_count += len(payloads)
        for payload in payloads:
            observations.extend(observe_bridge_payload(payload, p, root, decl_match_ctx))

    normalization, bridge_file_signals, bridge_decl_signals = normalize_bridge_observations(observations)

    theorem_by_name = {
        str(row.get("name")): row for row in theorem_entries if isinstance(row, dict) and row.get("name")
    }

    vacuity_candidates = rank_vacuity_candidates(
        theorem_entries=theorem_entries,
        module_region=module_region,
        file_region=file_region,
        hole_counts=hole_counts,
        bridge_file_signals=bridge_file_signals,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    owner_candidates = rank_owner_candidates(
        vacuity_candidates=vacuity_candidates,
        owner_entries=owner_entries,
        file_region=file_region,
        top_k=args.top_k,
    )

    replacement_candidates = rank_replacement_candidates(
        vacuity_candidates=vacuity_candidates,
        forward_edges=forward_edges,
        decls=decls,
        theorem_by_name=theorem_by_name,
        file_region=file_region,
        owner_candidates=owner_candidates,
        top_k=args.top_k,
    )

    fingerprint_corridors = rank_fingerprint_corridors(
        vacuity_candidates=vacuity_candidates,
        replacement_candidates=replacement_candidates,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    declaration_plans = rank_declaration_plans(
        vacuity_candidates=vacuity_candidates,
        owner_candidates=owner_candidates,
        replacement_candidates=replacement_candidates,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    admissibility_prechecks = rank_admissibility_prechecks(
        declaration_plans=declaration_plans,
        decls=decls,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    report: JsonObj = {
        "schema": "ig.vacuity-planner.v0",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "boundary": {
            "plannerMode": "planning-only",
            "mutationSurface": False,
            "automaticReplacement": False,
            "proofRepair": False,
            "strictAdmissibilityPrecheck": "scaffold-only",
        },
        "inputs": {
            "theoremSignificancePath": relpath_or_self(theorem_significance_path, root),
            "declsPath": relpath_or_self(decls_path, root),
            "edgesPath": relpath_or_self(edges_path, root),
            "moduleGraphPath": relpath_or_self(module_graph_path, root),
            "ownerIndexPath": relpath_or_self(owner_index_path, root),
            "proofHolesByFilePath": relpath_or_self(proof_holes_path, root) if proof_holes_path.exists() else None,
            "bridgeInputPaths": [relpath_or_self(p, root) for p in bridge_json_paths],
            "theoremSignificanceEntries": len(theorem_entries),
            "graphSourceRequested": args.graph_source,
            "graphSourceUsed": graph_source_used,
            "arangoNodesCollection": args.arango_nodes_collection if graph_source_used == "arango" else None,
            "arangoEdgesCollection": args.arango_edges_collection if graph_source_used == "arango" else None,
            "declarationCount": len(decls),
            "edgeCount": sum(len(v) for v in forward_edges.values()),
            "ownerEntries": len(owner_entries),
            "bridgePayloadFiles": len(bridge_json_paths),
            "bridgePayloadObjects": bridge_payload_count,
            "bridgeDeclarationSignalCount": len(bridge_decl_signals),
        },
        "normalization": normalization,
        "rankedVacuityCandidates": vacuity_candidates,
        "rankedOwnerCandidates": owner_candidates,
        "rankedReplacementCandidates": replacement_candidates,
        "rankedFingerprintCorridors": fingerprint_corridors,
        "rankedDeclarationPlans": declaration_plans,
        "rankedAdmissibilityPrechecks": admissibility_prechecks,
        "confidenceWeights": {
            "headSource": HEAD_SOURCE_WEIGHT,
            "diagnosticProvenance": DIAG_PROVENANCE_WEIGHT,
            "violationLevel": VIOLATION_LEVEL_WEIGHT,
        },
        "plannerPolicy": planner_policy_snapshot(),
    }

    out_json_path.parent.mkdir(parents=True, exist_ok=True)
    with out_json_path.open("w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    out_md_path.parent.mkdir(parents=True, exist_ok=True)
    with out_md_path.open("w", encoding="utf-8") as f:
        f.write(make_markdown_report(report))

    print(f"[vacuity-planner] JSON report -> {out_json_path}")
    print(f"[vacuity-planner] Markdown report -> {out_md_path}")
    print(
        "[vacuity-planner] summary: "
        f"vacuity={len(vacuity_candidates)}, "
        f"owners={len(owner_candidates)}, "
        f"replacements={len(replacement_candidates)}, "
        f"corridors={len(fingerprint_corridors)}, "
        f"declaration_plans={len(declaration_plans)}, "
        f"admissibility_prechecks={len(admissibility_prechecks)}, "
        f"bridge_payloads={bridge_payload_count}"
    )


if __name__ == "__main__":
    main()
