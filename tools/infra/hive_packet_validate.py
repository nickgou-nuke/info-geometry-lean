#!/usr/bin/env python3
"""Validate Hive packet JSON against repo-local machine-readable schemas."""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

import jsonschema
from jsonschema import RefResolver
from jsonschema import validators
from jsonschema.exceptions import ValidationError

ROOT = Path(__file__).resolve().parents[2]
SCHEMA_DIR = ROOT / "tools" / "schema" / "hive"
CONTRACT_SCHEMA = ROOT / "tools" / "schema" / "ground_truth_theorem_contract.schema.json"

SCHEMA_BY_KIND = {
    "BeeTask": SCHEMA_DIR / "BeeTask.schema.json",
    "BeeResult": SCHEMA_DIR / "BeeResult.schema.json",
    "SourceObservationPacket": SCHEMA_DIR / "SourceObservationPacket.schema.json",
    "SymbolicMotifPacket": SCHEMA_DIR / "SymbolicMotifPacket.schema.json",
    "SocraticQuestionPacket": SCHEMA_DIR / "SocraticQuestionPacket.schema.json",
    "SymbolicSeed": SCHEMA_DIR / "SymbolicSeed.schema.json",
    "FormulationVariant": SCHEMA_DIR / "FormulationVariant.schema.json",
    "ResonanceCluster": SCHEMA_DIR / "ResonanceCluster.schema.json",
    "PauliCritique": SCHEMA_DIR / "PauliCritique.schema.json",
    "InvariantDraft": SCHEMA_DIR / "InvariantDraft.schema.json",
    "TheoremCandidatePacket": SCHEMA_DIR / "TheoremCandidatePacket.schema.json",
    "TheoremBankEntryPacket": SCHEMA_DIR / "TheoremBankEntryPacket.schema.json",
    "OwnerAuditPacket": SCHEMA_DIR / "OwnerAuditPacket.schema.json",
    "ExternalTheoremCandidatePacket": SCHEMA_DIR / "ExternalTheoremCandidatePacket.schema.json",
    "TranslationPacket": SCHEMA_DIR / "TranslationPacket.schema.json",
    "RetrievalHypothesisPacket": SCHEMA_DIR / "RetrievalHypothesisPacket.schema.json",
    "ExecutionIntentPacket": SCHEMA_DIR / "ExecutionIntentPacket.schema.json",
    "LeanVerificationPacket": SCHEMA_DIR / "LeanVerificationPacket.schema.json",
    "PantographSessionEvidencePacket": SCHEMA_DIR / "PantographSessionEvidencePacket.schema.json",
    "BuildPacket": SCHEMA_DIR / "BuildPacket.schema.json",
    "AuditPacket": SCHEMA_DIR / "AuditPacket.schema.json",
    "ChatGPTSocraticAuditPacket": SCHEMA_DIR / "ChatGPTSocraticAuditPacket.schema.json",
    "PromotionDecisionPacket": SCHEMA_DIR / "PromotionDecisionPacket.schema.json",
    "ResiduePacket": SCHEMA_DIR / "ResiduePacket.schema.json",
    "RepairAttemptPacket": SCHEMA_DIR / "RepairAttemptPacket.schema.json",
    "AutoproofTracePacket": SCHEMA_DIR / "AutoproofTracePacket.schema.json",
    "RouteInvocationPacket": SCHEMA_DIR / "RouteInvocationPacket.schema.json",
    "TranslationControlPacket": SCHEMA_DIR / "TranslationControlPacket.schema.json",
}


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def build_store() -> dict[str, Any]:
    store: dict[str, Any] = {}
    for path in SCHEMA_DIR.glob("*.json"):
        schema = load_json(path)
        uri = schema.get("$id", path.name)
        store[uri] = schema
        store[path.name] = schema
    if CONTRACT_SCHEMA.is_file():
        schema = load_json(CONTRACT_SCHEMA)
        store[schema.get("$id", CONTRACT_SCHEMA.name)] = schema
        store[CONTRACT_SCHEMA.name] = schema
    return store


def choose_validator(schema: dict[str, Any], store: dict[str, Any]):
    validator_cls = validators.validator_for(schema)
    validator_cls.check_schema(schema)
    resolver = RefResolver.from_schema(schema, store=store)
    return validator_cls(schema, resolver=resolver)


def format_error(err: ValidationError) -> str:
    loc = "/".join(str(p) for p in err.absolute_path)
    if loc:
        return f"{loc}: {err.message}"
    return err.message


def validate_packet(packet: dict[str, Any], schema_path: Path, store: dict[str, Any]) -> list[str]:
    schema = load_json(schema_path)
    validator = choose_validator(schema, store)
    errors = sorted(validator.iter_errors(packet), key=lambda e: list(e.absolute_path))
    formatted = [format_error(e) for e in errors]
    if packet.get("kind") == "TheoremCandidatePacket" and "ground_truth_contract" in packet:
        formatted.extend(validate_ground_truth_candidate_integrity(packet))
    return formatted


def validate_ground_truth_candidate_integrity(packet: dict[str, Any]) -> list[str]:
    """Recompute the embedded contract and candidate hashes for bound packets."""
    from tools.infra.opengauss_ground_truth_contract import (
        canonical_digest, validate_contract_payload, validate_draft_receipt_payload,
    )

    binding = packet.get("ground_truth_contract")
    if not isinstance(binding, dict) or not isinstance(binding.get("contract"), dict):
        return ["ground_truth_contract must contain the full contract object"]
    contract = binding["contract"]
    try:
        checked = validate_contract_payload(contract, repo_root=ROOT)
    except ValueError as exc:
        return [f"ground_truth_contract is stale or invalid: {exc}"]
    digest = canonical_digest(contract)
    errors: list[str] = []
    formal_target = packet.get("formal_target")
    if not isinstance(formal_target, dict):
        errors.append("contract-bound candidate has no formal_target object")
    else:
        if formal_target.get("target_name") != checked["missing_declaration_name"]:
            errors.append("formal_target.target_name differs from the Ground-Truth Contract gap")
        if formal_target.get("target_expression") != checked["pantograph_expression"]:
            errors.append("formal_target.target_expression differs from the Ground-Truth Contract Pantograph expression")
    if binding.get("contract_sha256") != digest or checked["contract_sha256"] != digest:
        errors.append("ground_truth_contract.contract_sha256 does not match the embedded contract")
    draft_binding = packet.get("draft_binding")
    pantograph_binding = packet.get("pantograph_binding")
    if draft_binding is not None:
        if not isinstance(draft_binding, dict) or not isinstance(draft_binding.get("receipt"), dict):
            errors.append("draft_binding must contain a draft receipt object")
        else:
            receipt = draft_binding["receipt"]
            receipt_digest = canonical_digest(receipt)
            if draft_binding.get("receipt_sha256") != receipt_digest:
                errors.append("draft_binding.receipt_sha256 does not match its receipt")
            try:
                checked_draft = validate_draft_receipt_payload(receipt, repo_root=ROOT)
                if checked_draft["contract_sha256"] != digest:
                    errors.append("draft receipt contract differs from candidate contract")
                if not isinstance(formal_target, dict) or any(
                    formal_target.get(field) != checked_draft[expected]
                    for field, expected in (
                        ("target_name", "target_name"),
                        ("target_expression", "target_expression"),
                        ("source_path", "source_path"),
                        ("source_snapshot_sha256", "source_sha256"),
                    )
                ):
                    errors.append("formal_target does not match the validated draft receipt")
                expected_pantograph = {
                    "source_path": checked_draft["source_path"],
                    "source_snapshot_sha256": checked_draft["source_sha256"],
                    "target_expression": checked_draft["target_expression"],
                }
                if pantograph_binding != expected_pantograph:
                    errors.append("pantograph_binding does not match the validated draft receipt")
            except ValueError as exc:
                errors.append(f"draft receipt is stale or invalid: {exc}")
    elif pantograph_binding is not None:
        errors.append("pantograph_binding requires a source-validated draft_binding")
    material_keys = [
        "kind", "lineage_id", "symbolic_origin_refs", "formal_target", "bridge_claim",
        "novelty_defense", "repo_anchor_refs", "candidate_dependencies",
        "admissibility_state", "cost_class", "ground_truth_contract",
    ]
    material = {key: packet[key] for key in material_keys if key in packet}
    for optional_key in ("draft_binding", "pantograph_binding"):
        if optional_key in packet:
            material[optional_key] = packet[optional_key]
    expected_hash = "sha256:" + hashlib.sha256(
        json.dumps(material, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    ).hexdigest()[:32]
    if packet.get("packet_hash") != expected_hash:
        errors.append("TheoremCandidatePacket packet_hash does not cover its current contract binding")
    return errors


def cmd_validate(args: argparse.Namespace) -> int:
    packet_path = Path(args.packet)
    if not packet_path.exists():
        print(f"ERROR: packet not found: {packet_path}", file=sys.stderr)
        return 2
    packet = load_json(packet_path)
    if not isinstance(packet, dict):
        print("ERROR: packet must be a JSON object", file=sys.stderr)
        return 2

    schema_path: Path | None = None
    if args.schema:
        schema_path = Path(args.schema)
        if not schema_path.is_absolute():
            schema_path = (ROOT / args.schema).resolve()
        if not schema_path.exists():
            print(f"ERROR: schema not found: {schema_path}", file=sys.stderr)
            return 2
    else:
        kind = str(packet.get("kind", "")).strip()
        schema_path = SCHEMA_BY_KIND.get(kind)
        if schema_path is None:
            print(f"ERROR: unsupported or missing kind: {kind}", file=sys.stderr)
            print("Supported kinds:", ", ".join(sorted(SCHEMA_BY_KIND)), file=sys.stderr)
            return 2

    store = build_store()
    errors = validate_packet(packet, schema_path, store)
    if errors:
        print("INVALID hive packet")
        for error in errors:
            print(f"- {error}")
        return 1
    print(f"VALID hive packet ({schema_path.name})")
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_validate = sp.add_parser("validate", help="Validate a Hive packet JSON file.")
    p_validate.add_argument("--packet", required=True, help="Path to packet JSON.")
    p_validate.add_argument(
        "--schema",
        default="",
        help="Optional explicit schema path. If omitted, infer from packet.kind.",
    )
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.cmd == "validate":
        raise SystemExit(cmd_validate(args))
    raise SystemExit(2)


if __name__ == "__main__":
    main()
