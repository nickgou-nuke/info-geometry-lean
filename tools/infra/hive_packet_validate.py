#!/usr/bin/env python3
"""Validate Hive packet JSON against repo-local machine-readable schemas."""
from __future__ import annotations

import argparse
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
    "BuildPacket": SCHEMA_DIR / "BuildPacket.schema.json",
    "AuditPacket": SCHEMA_DIR / "AuditPacket.schema.json",
    "PromotionDecisionPacket": SCHEMA_DIR / "PromotionDecisionPacket.schema.json",
    "ResiduePacket": SCHEMA_DIR / "ResiduePacket.schema.json",
}


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def build_store() -> dict[str, Any]:
    store: dict[str, Any] = {}
    for path in SCHEMA_DIR.glob("*.json"):
        schema = load_json(path)
        uri = schema.get("$id", path.name)
        store[uri] = schema
        store[path.name] = schema
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
    return [format_error(e) for e in errors]


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
