#!/usr/bin/env python3
"""Normalize, validate, and split External Theorem Hive packet batches.

Input may be JSONL or a JSON array.  Each record must already be an
ExternalTheoremCandidatePacket; this tool is intentionally an ingest/validation
boundary, not an authority promoter.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

try:
    from tools.infra.hive_packet_build import stable_json
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ImportError:  # pragma: no cover - direct script execution
    ROOT_FOR_IMPORT = Path(__file__).resolve().parents[2]
    if str(ROOT_FOR_IMPORT) not in sys.path:
        sys.path.insert(0, str(ROOT_FOR_IMPORT))
    from tools.infra.hive_packet_build import stable_json
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

ROOT = Path(__file__).resolve().parents[2]
KIND = "ExternalTheoremCandidatePacket"


def read_records(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    stripped = text.lstrip()
    if not stripped:
        return []
    if stripped.startswith("["):
        payload = json.loads(text)
        if not isinstance(payload, list):
            raise SystemExit("ERROR: JSON array input must contain packet objects")
        records = payload
    else:
        records = [json.loads(line) for line in text.splitlines() if line.strip()]
    out = []
    for idx, record in enumerate(records, start=1):
        if not isinstance(record, dict):
            raise SystemExit(f"ERROR: record {idx} is not a JSON object")
        out.append(record)
    return out


def validate_records(records: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    schema = SCHEMA_BY_KIND[KIND]
    store = build_store()
    valid = []
    failures = []
    for idx, record in enumerate(records, start=1):
        if record.get("kind") != KIND:
            failures.append({"index": idx, "id": record.get("id", ""), "errors": [f"kind must be {KIND}"]})
            continue
        errors = validate_packet(record, schema, store)
        if errors:
            failures.append({"index": idx, "id": record.get("id", ""), "errors": errors})
            continue
        valid.append(record)
    return valid, failures


def write_outputs(args: argparse.Namespace, valid: list[dict[str, Any]], failures: list[dict[str, Any]]) -> None:
    out = Path(args.out)
    if not out.is_absolute():
        out = (ROOT / out).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8") as handle:
        for record in valid:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")

    split_dir = None
    if args.split_dir:
        split_dir = Path(args.split_dir)
        if not split_dir.is_absolute():
            split_dir = (ROOT / split_dir).resolve()
        split_dir.mkdir(parents=True, exist_ok=True)
        for record in valid:
            (split_dir / f"{record['id']}.json").write_text(stable_json(record), encoding="utf-8")

    manifest = {
        "kind": "ExternalTheoremHiveIngestManifest",
        "authority_boundary": "external theorem packets are proposal/navigation artifacts only; Lean/build/audit gates decide authority",
        "valid_count": len(valid),
        "failure_count": len(failures),
        "out": str(out),
        "split_dir": str(split_dir) if split_dir else "",
        "failures": failures,
    }
    manifest_path = Path(args.manifest) if args.manifest else out.with_suffix(out.suffix + ".manifest.json")
    if not manifest_path.is_absolute():
        manifest_path = (ROOT / manifest_path).resolve()
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(stable_json(manifest), encoding="utf-8")
    print(f"external theorem ingest valid={len(valid)} failed={len(failures)} out={out}")
    print(f"manifest: {manifest_path}")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, help="JSONL or JSON array of ExternalTheoremCandidatePacket objects.")
    p.add_argument("--out", required=True, help="Validated JSONL output path.")
    p.add_argument("--split-dir", default="", help="Optional directory for individual packet JSON files.")
    p.add_argument("--manifest", default="", help="Optional manifest output path.")
    p.add_argument("--fail-on-invalid", action="store_true", help="Exit nonzero if any packet fails validation.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    input_path = Path(args.input)
    if not input_path.is_absolute():
        input_path = (ROOT / input_path).resolve()
    records = read_records(input_path)
    valid, failures = validate_records(records)
    write_outputs(args, valid, failures)
    if failures and args.fail_on_invalid:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
