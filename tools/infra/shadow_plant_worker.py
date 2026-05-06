#!/usr/bin/env python3
"""Epistemic Reactor: gated shadow planting worker.

This is the first mutating phase of the epistemic reactor.  It consumes an
ensemble consensus packet and plants the result into append-only shadow
collections in ArangoDB.

Authority boundary:
  * input consensus is a proposal, not a proof;
  * planted rows receive authority `hive_purified`, not `lean_checked`;
  * shadow rows are navigation / scheduling material only;
  * promotion to theorem authority still requires Lean/build/audit gates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.arango_raw_infotree_ingest import (  # noqa: E402
    ArangoTarget,
    CollectionSpec,
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    create_collection,
    ensure_database,
    ensure_index,
    import_rows,
    list_collections,
    load_repo_arango_env,
)

CONSENSUS_SCHEMA = "info_geometry.epistemic_reactor.ensemble_consensus.v1"
REPORT_SCHEMA = "info_geometry.epistemic_reactor.shadow_plant_report.v1"
BATCH_SCHEMA = "info_geometry.epistemic_reactor.shadow_batch.v1"
NODE_SCHEMA = "info_geometry.epistemic_reactor.shadow_node.v1"
EDGE_SCHEMA = "info_geometry.epistemic_reactor.shadow_edge.v1"

BATCH_COLLECTION = "hive_purified_shadow_batches"
NODE_COLLECTION = "hive_purified_shadow_nodes"
EDGE_COLLECTION = "hive_purified_shadow_edges"

SHADOW_AUTHORITY = "hive_purified"
PROPOSAL_AUTHORITIES = {"proposal", "navigation", "retrieval_only", "semantic"}
FORBIDDEN_PROMOTED_AUTHORITIES = {
    "lean_checked",
    "build_checked",
    "audit_checked",
    "promotion_decided",
    "promoted",
    "kernel_proved",
}

AUTHORITY_BOUNDARY = {
    "shadow_is_not_proof": True,
    "hive_purified_is_not_lean_checked": True,
    "graph_material_is_navigation_only": True,
    "lean_remains_proof_authority": True,
    "audits_admit_before_promotion": True,
}


def canonical_json(value: Any) -> str:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )


def stable_key(prefix: str, value: Any, size: int = 32) -> str:
    digest = hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()
    return f"{prefix}_{digest[:size]}"


def read_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON input {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise SystemExit(f"expected a JSON object in {path}")
    return data


def require_safe_consensus(packet: dict[str, Any], allow_empty: bool) -> list[str]:
    failures: list[str] = []
    schema = packet.get("schema")
    authority = packet.get("authority")
    boundary = packet.get("authority_boundary")

    if schema != CONSENSUS_SCHEMA:
        failures.append(f"schema must be {CONSENSUS_SCHEMA!r}, got {schema!r}")
    if authority not in PROPOSAL_AUTHORITIES:
        failures.append(
            f"authority must remain proposal/navigation before planting, got {authority!r}"
        )
    if authority in FORBIDDEN_PROMOTED_AUTHORITIES:
        failures.append(f"forbidden promoted authority on input: {authority!r}")
    if not isinstance(boundary, dict):
        failures.append("authority_boundary must be present")
    else:
        if not boundary.get("consensus_is_not_truth", False):
            failures.append("authority_boundary.consensus_is_not_truth must be true")
        if not boundary.get("lean_remains_proof_authority", False):
            failures.append("authority_boundary.lean_remains_proof_authority must be true")

    source_packet_id = packet.get("source_packet_id") or packet.get("packet_id")
    if not source_packet_id:
        failures.append("source_packet_id or packet_id is required")

    items = extract_consensus_items(packet)
    if not allow_empty and not items:
        failures.append("no consensus items found; use --allow-empty to plant an empty batch")

    forbidden_claims = packet.get("forbidden_authority_claims", [])
    if not isinstance(forbidden_claims, list):
        failures.append("forbidden_authority_claims must be a list when present")

    return failures


def extract_consensus_items(packet: dict[str, Any]) -> list[dict[str, Any]]:
    """Support the repo-native consensus format and older metric-only packets."""
    native = packet.get("consensus_items")
    if isinstance(native, list):
        return [item for item in native if isinstance(item, dict)]

    metrics = packet.get("consensus_metrics")
    if not isinstance(metrics, dict):
        return []

    items: list[dict[str, Any]] = []
    for action in metrics.get("consensus_actions", []) or []:
        if isinstance(action, str):
            items.append(
                {
                    "kind": "action",
                    "claim": action,
                    "support_fraction": 1.0,
                    "source": "consensus_metrics.consensus_actions",
                }
            )
    for edge in metrics.get("consensus_edges", []) or []:
        if isinstance(edge, dict):
            source = str(edge.get("source", "unknown"))
            target = str(edge.get("target", "unknown"))
            relation = str(edge.get("type", "related_to"))
            items.append(
                {
                    "kind": "edge",
                    "claim": f"{source} --{relation}--> {target}",
                    "source": source,
                    "target": target,
                    "relation": relation,
                    "support_fraction": edge.get("consensus_score", 1.0),
                    "source_format": "consensus_metrics.consensus_edges",
                }
            )
    return items


def ensure_shadow_collections(target: ArangoTarget) -> None:
    existing = set(list_collections(target))
    specs = [
        CollectionSpec(BATCH_COLLECTION, "document"),
        CollectionSpec(NODE_COLLECTION, "document"),
        CollectionSpec(EDGE_COLLECTION, "edge"),
    ]
    for spec in specs:
        if spec.name not in existing:
            create_collection(target, spec)

    ensure_index(target, BATCH_COLLECTION, ["source_packet_id"])
    ensure_index(target, BATCH_COLLECTION, ["consensus_id"])
    ensure_index(target, BATCH_COLLECTION, ["authority"])
    ensure_index(target, NODE_COLLECTION, ["source_packet_id"])
    ensure_index(target, NODE_COLLECTION, ["consensus_id"])
    ensure_index(target, NODE_COLLECTION, ["authority"])
    ensure_index(target, NODE_COLLECTION, ["promotion_state"])
    ensure_index(target, NODE_COLLECTION, ["kind"])
    ensure_index(target, EDGE_COLLECTION, ["type"])
    ensure_index(target, EDGE_COLLECTION, ["authority"])
    ensure_index(target, EDGE_COLLECTION, ["source_packet_id"])


def build_rows(packet: dict[str, Any], input_path: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    now = datetime.now(timezone.utc).isoformat()
    source_packet_id = str(packet.get("source_packet_id") or packet.get("packet_id"))
    consensus_id = str(packet.get("consensus_id") or packet.get("packet_id") or stable_key("consensus", packet))
    consensus_items = extract_consensus_items(packet)
    forbidden_claims = packet.get("forbidden_authority_claims", [])
    shadow_template = packet.get("shadow_merge_template")

    batch_key = stable_key(
        "shadow_batch",
        {
            "source_packet_id": source_packet_id,
            "consensus_id": consensus_id,
            "schema": packet.get("schema"),
        },
    )
    batch = {
        "_key": batch_key,
        "schema": BATCH_SCHEMA,
        "authority": SHADOW_AUTHORITY,
        "promotion_state": "shadow_only",
        "source_packet_id": source_packet_id,
        "consensus_id": consensus_id,
        "source_consensus_path": str(input_path),
        "created_at": now,
        "counts": {
            "consensus_items": len(consensus_items),
        },
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
        "input_authority_boundary": packet.get("authority_boundary"),
        "forbidden_authority_claims": forbidden_claims,
        "shadow_merge_template": shadow_template,
    }

    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    batch_id = f"{BATCH_COLLECTION}/{batch_key}"
    for index, item in enumerate(consensus_items):
        claim = str(item.get("claim") or item.get("proposed_action") or item.get("content") or item)
        kind = str(item.get("kind") or item.get("type") or "consensus_item")
        node_key = stable_key(
            "shadow_node",
            {
                "source_packet_id": source_packet_id,
                "consensus_id": consensus_id,
                "index": index,
                "kind": kind,
                "claim": claim,
            },
        )
        node = {
            "_key": node_key,
            "schema": NODE_SCHEMA,
            "authority": SHADOW_AUTHORITY,
            "promotion_state": "shadow_only",
            "source_packet_id": source_packet_id,
            "consensus_id": consensus_id,
            "batch_key": batch_key,
            "created_at": now,
            "kind": kind,
            "claim": claim,
            "support_fraction": item.get("support_fraction"),
            "support_count": item.get("support_count"),
            "risk": item.get("risk", "proposal"),
            "source_refs": item.get("source_refs", []),
            "lean_owner_candidates": item.get("lean_owner_candidates", []),
            "required_descent": item.get("required_descent", "raw_lean_witness"),
            "payload": item,
            "authority_boundary": dict(AUTHORITY_BOUNDARY),
            "forbidden_authority_claims": forbidden_claims,
        }
        nodes.append(node)
        edges.append(
            {
                "_key": stable_key(
                    "shadow_edge",
                    {
                        "batch": batch_key,
                        "node": node_key,
                        "type": "BATCH_EMITS_SHADOW",
                    },
                ),
                "_from": batch_id,
                "_to": f"{NODE_COLLECTION}/{node_key}",
                "schema": EDGE_SCHEMA,
                "authority": SHADOW_AUTHORITY,
                "promotion_state": "shadow_only",
                "source_packet_id": source_packet_id,
                "consensus_id": consensus_id,
                "created_at": now,
                "type": "BATCH_EMITS_SHADOW",
                "authority_boundary": dict(AUTHORITY_BOUNDARY),
            }
        )

    return [batch], nodes, edges


def write_report(
    path: Path,
    *,
    input_path: Path,
    dry_run: bool,
    failures: list[str],
    batch_count: int,
    node_count: int,
    edge_count: int,
    target: ArangoTarget | None,
) -> dict[str, Any]:
    report = {
        "schema": REPORT_SCHEMA,
        "input": str(input_path),
        "dry_run": dry_run,
        "ok": not failures,
        "failures": failures,
        "collections": {
            "batches": BATCH_COLLECTION,
            "nodes": NODE_COLLECTION,
            "edges": EDGE_COLLECTION,
        },
        "counts": {
            "batches": batch_count,
            "nodes": node_count,
            "edges": edge_count,
        },
        "target": None
        if target is None
        else {
            "endpoint": target.endpoint,
            "database": target.database,
            "username": target.username,
        },
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Plant ensemble consensus into hive_purified shadow Arango collections."
    )
    parser.add_argument("--input", required=True, type=Path, help="ensemble_consensus.json")
    parser.add_argument(
        "--json-out",
        type=Path,
        default=REPO_ROOT / "reports/dag/shadow-plant-worker.json",
        help="Write a JSON receipt/report.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Build rows but do not mutate ArangoDB.")
    parser.add_argument("--allow-empty", action="store_true", help="Allow planting an empty shadow batch.")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--arango-endpoint")
    parser.add_argument("--arango-database")
    parser.add_argument("--arango-username")
    parser.add_argument("--arango-password")
    args = parser.parse_args(argv)

    packet = read_json(args.input)
    failures = require_safe_consensus(packet, allow_empty=args.allow_empty)
    batch_rows, node_rows, edge_rows = build_rows(packet, args.input)

    target: ArangoTarget | None = None
    if failures:
        report = write_report(
            args.json_out,
            input_path=args.input,
            dry_run=args.dry_run,
            failures=failures,
            batch_count=len(batch_rows),
            node_count=len(node_rows),
            edge_count=len(edge_rows),
            target=None,
        )
        print(json.dumps(report, indent=2, ensure_ascii=False))
        return 1

    load_repo_arango_env(REPO_ROOT)
    target = ArangoTarget(
        endpoint=args.arango_endpoint or arango_endpoint(),
        database=args.arango_database or arango_database(),
        username=args.arango_username or arango_username(),
        password=args.arango_password or arango_password(),
    )

    if not args.dry_run:
        ensure_database(target)
        ensure_shadow_collections(target)
        import_rows(target, BATCH_COLLECTION, batch_rows, batch_size=args.batch_size)
        import_rows(target, NODE_COLLECTION, node_rows, batch_size=args.batch_size)
        import_rows(target, EDGE_COLLECTION, edge_rows, batch_size=args.batch_size)

    report = write_report(
        args.json_out,
        input_path=args.input,
        dry_run=args.dry_run,
        failures=[],
        batch_count=len(batch_rows),
        node_count=len(node_rows),
        edge_count=len(edge_rows),
        target=target,
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
