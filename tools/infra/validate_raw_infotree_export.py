#!/usr/bin/env python3
"""Validate the stage-1 raw InfoTree export contract.

This checks topology preservation surfaces, not mathematical truth. It ensures
that an export directory contains the required `raw_infotree_*` files and that
parent-child edges reference emitted nodes with sibling indices.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


REQUIRED_FILES = [
    "raw_infotree_roots.jsonl",
    "raw_infotree_nodes.jsonl",
    "raw_infotree_edges.jsonl",
    "raw_infotree_contexts.jsonl",
    "raw_infotree_payloads.jsonl",
    "raw_infotree_payload_fields.jsonl",
    "raw_infotree_decl_links.jsonl",
    "raw_infotree_env_refs.jsonl",
    "raw_infotree_mctx_refs.jsonl",
    "raw_infotree_mctx_decls.jsonl",
    "raw_infotree_lctx_refs.jsonl",
    "raw_infotree_lctx_decls.jsonl",
    "raw_infotree_goal_states.jsonl",
    "raw_infotree_fvar_lineage.jsonl",
    "raw_infotree_tactic_arguments.jsonl",
    "raw_infotree_messages.jsonl",
    "raw_infotree_projection_leakage.jsonl",
    "metadata.json",
]


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            rows.append(row)
    return rows


def validate(input_dir: Path) -> dict[str, Any]:
    missing = [name for name in REQUIRED_FILES if not (input_dir / name).exists()]
    errors: list[str] = [f"missing required file: {name}" for name in missing]

    roots = read_jsonl(input_dir / "raw_infotree_roots.jsonl") if not missing else []
    nodes = read_jsonl(input_dir / "raw_infotree_nodes.jsonl") if not missing else []
    edges = read_jsonl(input_dir / "raw_infotree_edges.jsonl") if not missing else []
    payloads = read_jsonl(input_dir / "raw_infotree_payloads.jsonl") if not missing else []
    payload_fields = read_jsonl(input_dir / "raw_infotree_payload_fields.jsonl") if not missing else []
    contexts = read_jsonl(input_dir / "raw_infotree_contexts.jsonl") if not missing else []
    decl_links = read_jsonl(input_dir / "raw_infotree_decl_links.jsonl") if not missing else []
    env_refs = read_jsonl(input_dir / "raw_infotree_env_refs.jsonl") if not missing else []
    mctx_refs = read_jsonl(input_dir / "raw_infotree_mctx_refs.jsonl") if not missing else []
    mctx_decls = read_jsonl(input_dir / "raw_infotree_mctx_decls.jsonl") if not missing else []
    lctx_refs = read_jsonl(input_dir / "raw_infotree_lctx_refs.jsonl") if not missing else []
    lctx_decls = read_jsonl(input_dir / "raw_infotree_lctx_decls.jsonl") if not missing else []
    goal_states = read_jsonl(input_dir / "raw_infotree_goal_states.jsonl") if not missing else []
    fvar_lineage = read_jsonl(input_dir / "raw_infotree_fvar_lineage.jsonl") if not missing else []
    tactic_arguments = read_jsonl(input_dir / "raw_infotree_tactic_arguments.jsonl") if not missing else []
    messages = read_jsonl(input_dir / "raw_infotree_messages.jsonl") if not missing else []
    leakage = read_jsonl(input_dir / "raw_infotree_projection_leakage.jsonl") if not missing else []
    metadata = {}
    if not missing:
        metadata = json.loads((input_dir / "metadata.json").read_text(encoding="utf-8"))
    fully_lossless = metadata.get("fully_lossless") is True

    root_keys = {str(row.get("rootKey")) for row in roots}
    roots_by_key = {str(row.get("rootKey")): row for row in roots}
    node_keys = {str(row.get("nodeKey")) for row in nodes}
    nodes_by_key = {str(row.get("nodeKey")): row for row in nodes}
    payload_keys = {str(row.get("payloadKey")) for row in payloads}
    mctx_ref_keys = {str(row.get("mctxRefKey")) for row in mctx_refs}
    mctx_keys = {str(row.get("mctxKey")) for row in mctx_refs}
    mctx_decl_keys = {str(row.get("declKey")) for row in mctx_decls}
    lctx_ref_keys = {str(row.get("lctxRefKey")) for row in lctx_refs}
    lctx_keys = {str(row.get("lctxKey")) for row in lctx_refs}
    goal_state_keys = {str(row.get("stateKey")) for row in goal_states}
    payload_keys_by_node = {str(row.get("nodeKey")): str(row.get("payloadKey")) for row in payloads}

    def opt_field(row: dict[str, Any], name: str) -> Any:
        return row.get(name) if name in row else row.get(f"{name}?")

    def validate_node_provenance(row: dict[str, Any], row_id: str) -> None:
        node = str(row.get("nodeKey"))
        node_row = nodes_by_key.get(node)
        if node_row is None:
            return
        root_key = str(node_row.get("rootKey"))
        root_row = roots_by_key.get(root_key)
        if root_row is None:
            return
        if row.get("rootKey") != root_key:
            errors.append(f"{row_id} rootKey does not match node/root join path")
        if row.get("file") != root_row.get("file"):
            errors.append(f"{row_id} file does not match root file")
        if row.get("module") != root_row.get("module"):
            errors.append(f"{row_id} module does not match root module")

    for row in nodes:
        root_key = str(row.get("rootKey"))
        if root_key not in root_keys:
            errors.append(f"node {row.get('nodeKey')} references missing root {root_key}")
        parent = opt_field(row, "parentKey")
        if parent is not None and str(parent) not in node_keys:
            errors.append(f"node {row.get('nodeKey')} references missing parent {parent}")
        payload = opt_field(row, "payloadKey")
        if payload is not None and str(payload) not in payload_keys:
            errors.append(f"node {row.get('nodeKey')} references missing payload {payload}")
        hole_mvar = opt_field(row, "holeMVarId")
        if row.get("kind") == "hole":
            if not isinstance(hole_mvar, str) or not hole_mvar:
                errors.append(f"hole node {row.get('nodeKey')} is missing holeMVarId")
        elif hole_mvar is not None:
            errors.append(f"non-hole node {row.get('nodeKey')} carries holeMVarId")

    edge_pairs: set[tuple[str, str, int]] = set()
    for row in edges:
        parent = str(row.get("parentKey"))
        child = str(row.get("childKey"))
        sibling = row.get("siblingIndex")
        if parent not in node_keys:
            errors.append(f"edge {row.get('edgeKey')} references missing parent {parent}")
        if child not in node_keys:
            errors.append(f"edge {row.get('edgeKey')} references missing child {child}")
        if not isinstance(sibling, int):
            errors.append(f"edge {row.get('edgeKey')} has non-integer siblingIndex")
            sibling = -1
        marker = (parent, child, sibling)
        if marker in edge_pairs:
            errors.append(f"duplicate parent-child-sibling edge: {marker}")
        edge_pairs.add(marker)

    for row in contexts:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"context {row.get('contextKey')} references missing node {node}")
        validate_node_provenance(row, f"context {row.get('contextKey')}")
        context_kind = row.get("contextKind")
        if context_kind is None and (row.get("lctx_size") == 0 or row.get("mctx_size") == 0):
            errors.append(
                f"context {row.get('contextKey')} uses numeric zero for unknown context size; "
                "unknown compiler state must be null/absent, not 0"
            )
        if row.get("lctx_size") == 0:
            errors.append(
                f"context {row.get('contextKey')} stores lctx_size=0 without a Lean-exposed "
                "context-row local-context source; omit it unless it is a real measurement"
            )

    for row in decl_links:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"decl link {row.get('linkKey')} references missing node {node}")
        validate_node_provenance(row, f"decl link {row.get('linkKey')}")
        decl_name = row.get("declName")
        if not isinstance(decl_name, str) or not decl_name:
            errors.append(f"decl link {row.get('linkKey')} has empty declName")

    for row in payloads:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"payload {row.get('payloadKey')} references missing node {node}")
        validate_node_provenance(row, f"payload {row.get('payloadKey')}")
        kind = row.get("kind")
        if not isinstance(kind, str) or not kind:
            errors.append(f"payload {row.get('payloadKey')} has empty kind")
        text = row.get("text")
        if not isinstance(text, str):
            errors.append(f"payload {row.get('payloadKey')} has non-string text")

    for row in payload_fields:
        payload = str(row.get("payloadKey"))
        node = str(row.get("nodeKey"))
        payload_row = None
        if payload not in payload_keys:
            errors.append(f"payload field {row.get('fieldKey')} references missing payload {payload}")
        else:
            payload_row = next((item for item in payloads if str(item.get("payloadKey")) == payload), None)
        if node not in node_keys:
            errors.append(f"payload field {row.get('fieldKey')} references missing node {node}")
        validate_node_provenance(row, f"payload field {row.get('fieldKey')}")
        if payload_row is not None:
            if row.get("rootKey") != payload_row.get("rootKey"):
                errors.append(f"payload field {row.get('fieldKey')} rootKey does not match payload")
            if row.get("file") != payload_row.get("file"):
                errors.append(f"payload field {row.get('fieldKey')} file does not match payload")
            if row.get("module") != payload_row.get("module"):
                errors.append(f"payload field {row.get('fieldKey')} module does not match payload")
        field = row.get("field")
        if not isinstance(field, str) or not field:
            errors.append(f"payload field {row.get('fieldKey')} has empty field name")
        value = row.get("value")
        if not isinstance(value, str):
            errors.append(f"payload field {row.get('fieldKey')} has non-string value")

    for row in env_refs:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"env ref {row.get('envRefKey')} references missing node {node}")
        validate_node_provenance(row, f"env ref {row.get('envRefKey')}")
        role = row.get("role")
        if role not in {"env", "cmdEnv"}:
            errors.append(f"env ref {row.get('envRefKey')} has invalid role {role!r}")
        if not isinstance(row.get("present"), bool):
            errors.append(f"env ref {row.get('envRefKey')} has non-boolean present field")
        if row.get("present"):
            for field in ("directImportCount", "allImportedModuleCount"):
                if not isinstance(opt_field(row, field), int):
                    errors.append(f"env ref {row.get('envRefKey')} has non-integer {field}")
            for field in ("directImportsHash", "allImportedModulesHash"):
                value = opt_field(row, field)
                if value is not None and not isinstance(value, int):
                    errors.append(f"env ref {row.get('envRefKey')} has non-integer {field}")

    for row in mctx_refs:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"mctx ref {row.get('mctxRefKey')} references missing node {node}")
        validate_node_provenance(row, f"mctx ref {row.get('mctxRefKey')}")
        if not isinstance(row.get("mctxKey"), str) or not row.get("mctxKey"):
            errors.append(f"mctx ref {row.get('mctxRefKey')} has empty mctxKey")
        for field in (
            "depth",
            "levelAssignDepth",
            "mvarCounter",
            "declCount",
            "levelDepthCount",
            "userNameCount",
            "levelAssignmentCount",
            "exprAssignmentCount",
            "delayedAssignmentCount",
            "declIdsHash",
            "userNamesHash",
        ):
            if not isinstance(row.get(field), int):
                errors.append(f"mctx ref {row.get('mctxRefKey')} has non-integer {field}")

    mctx_decls_by_key: dict[str, list[dict[str, Any]]] = {}
    for row in mctx_decls:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"mctx decl {row.get('declKey')} references missing node {node}")
        validate_node_provenance(row, f"mctx decl {row.get('declKey')}")
        mctx_key = str(row.get("mctxKey"))
        mctx_decls_by_key.setdefault(mctx_key, []).append(row)
        if mctx_key not in mctx_keys:
            errors.append(f"mctx decl {row.get('declKey')} references missing mctx key {mctx_key}")
        for field in (
            "mvarId",
            "userName",
            "kind",
            "typeText",
        ):
            if not isinstance(row.get(field), str):
                errors.append(f"mctx decl {row.get('declKey')} has non-string {field}")
        for field in (
            "depth",
            "index",
            "numScopeArgs",
            "lctxSize",
            "localInstanceCount",
            "typeHash",
        ):
            if not isinstance(row.get(field), int):
                errors.append(f"mctx decl {row.get('declKey')} has non-integer {field}")
        for field in ("assigned", "delayedAssigned"):
            if not isinstance(row.get(field), bool):
                errors.append(f"mctx decl {row.get('declKey')} has non-boolean {field}")
        if row.get("assigned"):
            if not isinstance(row.get("assignmentText"), str):
                errors.append(f"mctx decl {row.get('declKey')} is assigned without assignmentText")
            if not isinstance(row.get("assignmentHash"), int):
                errors.append(f"mctx decl {row.get('declKey')} is assigned without assignmentHash")
        if row.get("delayedAssigned"):
            if not isinstance(row.get("delayedPendingMVar"), str):
                errors.append(f"mctx decl {row.get('declKey')} is delayed without delayedPendingMVar")
            if not isinstance(row.get("delayedFVarCount"), int):
                errors.append(f"mctx decl {row.get('declKey')} is delayed without delayedFVarCount")

    for row in mctx_refs:
        mctx_ref = str(row.get("mctxRefKey"))
        mctx_key = str(row.get("mctxKey"))
        decl_rows = mctx_decls_by_key.get(mctx_key, [])
        decl_count = row.get("declCount")
        if isinstance(decl_count, int) and len(decl_rows) != decl_count:
            errors.append(
                f"mctx ref {mctx_ref} / mctxKey {mctx_key} declares declCount={decl_count} but "
                f"raw_infotree_mctx_decls has {len(decl_rows)} rows"
            )
        decl_ids_text = row.get("declIdsText")
        if isinstance(decl_ids_text, str):
            expected_ids = {line for line in decl_ids_text.splitlines() if line}
            actual_ids = {
                str(decl_row.get("mvarId"))
                for decl_row in decl_rows
                if isinstance(decl_row.get("mvarId"), str)
            }
            if actual_ids != expected_ids:
                errors.append(
                    f"mctx ref {mctx_ref} declIdsText does not match "
                    "raw_infotree_mctx_decls mvarId set"
                )

    for row in lctx_refs:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"lctx ref {row.get('lctxRefKey')} references missing node {node}")
        validate_node_provenance(row, f"lctx ref {row.get('lctxRefKey')}")
        source_kind = row.get("sourceKind")
        source_key = row.get("sourceKey")
        if not isinstance(row.get("lctxRefKey"), str) or not row.get("lctxRefKey"):
            errors.append("lctx ref has empty lctxRefKey")
        if not isinstance(row.get("lctxKey"), str) or not row.get("lctxKey"):
            errors.append(f"lctx ref {row.get('lctxRefKey')} has empty lctxKey")
        if not isinstance(row.get("lctxSize"), int):
            errors.append(f"lctx ref {row.get('lctxRefKey')} has non-integer lctxSize")
        if source_kind == "mctx_decl" and str(source_key) not in mctx_decl_keys:
            errors.append(f"lctx ref {row.get('lctxRefKey')} references missing mctx decl source {source_key}")
        if source_kind != "mctx_decl" and node in payload_keys_by_node:
            payload_key = payload_keys_by_node[node]
            if not str(source_key).startswith(f"itlcs_{payload_key}_"):
                errors.append(
                    f"lctx ref {row.get('lctxRefKey')} sourceKey does not descend from node payload"
                )

    for row in lctx_decls:
        node = str(row.get("nodeKey"))
        if node not in node_keys:
            errors.append(f"lctx decl {row.get('lctxDeclKey')} references missing node {node}")
        validate_node_provenance(row, f"lctx decl {row.get('lctxDeclKey')}")
        source_kind = row.get("sourceKind")
        source_key = row.get("sourceKey")
        if not isinstance(source_kind, str) or not source_kind:
            errors.append(f"lctx decl {row.get('lctxDeclKey')} has empty sourceKind")
        if not isinstance(source_key, str) or not source_key:
            errors.append(f"lctx decl {row.get('lctxDeclKey')} has empty sourceKey")
        if source_kind != "lctx_context":
            errors.append(f"lctx decl {row.get('lctxDeclKey')} has invalid sourceKind {source_kind!r}")
        if str(source_key) not in lctx_keys:
            errors.append(f"lctx decl {row.get('lctxDeclKey')} references missing lctx context {source_key}")
        for field in (
            "fvarId",
            "userName",
            "localDeclKind",
            "typeText",
        ):
            if not isinstance(row.get(field), str):
                errors.append(f"lctx decl {row.get('lctxDeclKey')} has non-string {field}")
        for field in ("index", "typeHash"):
            if not isinstance(row.get(field), int):
                errors.append(f"lctx decl {row.get('lctxDeclKey')} has non-integer {field}")
        if not isinstance(row.get("isLet"), bool):
            errors.append(f"lctx decl {row.get('lctxDeclKey')} has non-boolean isLet")
        if row.get("valueText") is not None and not isinstance(row.get("valueText"), str):
            errors.append(f"lctx decl {row.get('lctxDeclKey')} has non-string valueText")
        if row.get("valueHash") is not None and not isinstance(row.get("valueHash"), int):
            errors.append(f"lctx decl {row.get('lctxDeclKey')} has non-integer valueHash")

    parentful_nodes = [row for row in nodes if opt_field(row, "parentKey") is not None]
    if len(parentful_nodes) != len(edges):
        errors.append(
            f"parentful node count {len(parentful_nodes)} does not match edge count {len(edges)}"
        )

    # Validate goal states
    for row in goal_states:
        validate_node_provenance(row, f"goal_state {row.get('stateKey')}")
        node_key = str(row.get("nodeKey"))
        if node_key not in node_keys:
            errors.append(f"goal_state {row.get('stateKey')} nodeKey not found")
        if row.get("role") not in ["before", "after"]:
            errors.append(f"goal_state {row.get('stateKey')} invalid role")

    # Validate fvar lineage
    for row in fvar_lineage:
        validate_node_provenance(row, f"fvar_lineage {row.get('lineageKey')}")
        node_key = str(row.get("nodeKey"))
        if node_key not in node_keys:
            errors.append(f"fvar_lineage {row.get('lineageKey')} nodeKey not found")
        if row.get("role") not in ["intro", "consume"]:
            errors.append(f"fvar_lineage {row.get('lineageKey')} invalid role")

    # Validate tactic arguments
    for row in tactic_arguments:
        validate_node_provenance(row, f"tactic_argument {row.get('argumentKey')}")
        node_key = str(row.get("nodeKey"))
        if node_key not in node_keys:
            errors.append(f"tactic_argument {row.get('argumentKey')} nodeKey not found")

    # Validate messages
    for row in messages:
        node_key = row.get("nodeKey")
        if node_key is not None and str(node_key) not in node_keys:
            errors.append(f"message {row.get('messageKey')} nodeKey not found")

    # Validate node fields
    for row in nodes:
        if "isLogical" not in row:
            errors.append(f"node {row.get('nodeKey')} missing isLogical field")
        if "depth" not in row:
            errors.append(f"node {row.get('nodeKey')} missing depth field")
        if "branchingFactor" not in row:
            errors.append(f"node {row.get('nodeKey')} missing branchingFactor field")
        for pos in ["startPos", "endPos"]:
            val = opt_field(row, pos)
            if val is not None and not isinstance(val, int):
                errors.append(f"node {row.get('nodeKey')} {pos} must be Nat or None")

    report = {
        "schema": "info_geometry.raw_infotree_export_validation.v1",
        "input_dir": str(input_dir),
        "ok": not errors,
        "topology_ok": not errors,
        "lossless_ok": fully_lossless and len(leakage) == 0,
        "lossless_errors": [] if fully_lossless and len(leakage) == 0 else [
            *([] if fully_lossless else ["metadata fully_lossless is not true"]),
            *([] if len(leakage) == 0 else [f"leakage rows present: {len(leakage)}"]),
        ],
        "errors": errors,
        "counts": {
            "roots": len(roots),
            "nodes": len(nodes),
            "edges": len(edges),
            "contexts": len(contexts),
            "payloads": len(payloads),
            "payload_fields": len(payload_fields),
            "decl_links": len(decl_links),
            "env_refs": len(env_refs),
            "mctx_refs": len(mctx_refs),
            "mctx_decls": len(mctx_decls),
            "lctx_refs": len(lctx_refs),
            "lctx_decls": len(lctx_decls),
            "goal_states": len(goal_states),
            "fvar_lineage": len(fvar_lineage),
            "tactic_arguments": len(tactic_arguments),
            "messages": len(messages),
            "leakage": len(leakage),
        },
        "metadata": metadata,
    }
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument(
        "--require-lossless",
        action="store_true",
        help="Fail unless metadata fully_lossless=true and no leakage rows are present.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    report = validate(args.input_dir.resolve())
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, ensure_ascii=True))
    if not report["ok"]:
        return 2
    if args.require_lossless and not report["lossless_ok"]:
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
