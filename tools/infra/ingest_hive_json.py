#!/usr/bin/env python3
"""Extract, normalize, and persist HIVE_JSON packets emitted by HiveLogos."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = REPO_ROOT / "artifacts" / "hermes_loop" / "hive_memory" / "latest.jsonl"
DEFAULT_MANIFEST = REPO_ROOT / "artifacts" / "hermes_loop" / "hive_memory" / "latest.manifest.json"
HIVE_PREFIX = "HIVE_JSON "
RECORD_SCHEMA = "info_geometry.hive_memory.v1"


class HiveIngestError(RuntimeError):
    pass


def parse_hive_lines(text: str) -> list[tuple[int, dict[str, Any]]]:
    packets: list[tuple[int, dict[str, Any]]] = []
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if not line.startswith(HIVE_PREFIX):
            continue
        payload_text = line[len(HIVE_PREFIX) :].strip()
        try:
            payload = json.loads(payload_text)
        except json.JSONDecodeError as exc:
            raise HiveIngestError(f"invalid HIVE_JSON payload on line {line_number}: {exc}") from exc
        if not isinstance(payload, dict):
            raise HiveIngestError(f"expected JSON object on line {line_number}")
        packets.append((line_number, payload))
    return packets


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def shape_for_packet(packet: dict[str, Any]) -> str:
    for key in (
        "targetHashShapeCanonical",
        "conclusionHashShapeCanonical",
        "fullTypeHashShapeCanonical",
        "canonicalPreimage",
    ):
        value = packet.get(key)
        if isinstance(value, str) and value:
            return value
    return ""


def entity_key_for_packet(packet: dict[str, Any]) -> str:
    const_name = packet.get("constName")
    if isinstance(const_name, str) and const_name:
        return const_name
    module_name = packet.get("module")
    goal_index = packet.get("goalIndex")
    if isinstance(module_name, str) and module_name and isinstance(goal_index, int):
        return f"{module_name}:{goal_index}"
    artifact_kind = packet.get("artifactKind")
    if isinstance(artifact_kind, str) and artifact_kind:
        return artifact_kind
    return "unknown"


def build_record(*, packet: dict[str, Any], line_number: int, packet_index: int, source: str) -> dict[str, Any]:
    canonical_shape = shape_for_packet(packet)
    packet_bytes = canonical_json_bytes(packet)
    return {
        "schema": RECORD_SCHEMA,
        "source": source,
        "line_number": line_number,
        "packet_index": packet_index,
        "artifact_kind": packet.get("artifactKind", ""),
        "space": packet.get("space", ""),
        "entity_key": entity_key_for_packet(packet),
        "canonical_shape": canonical_shape,
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "shape_sha256": hashlib.sha256(canonical_shape.encode("utf-8")).hexdigest(),
        "packet": packet,
    }


def ingest_text(text: str, *, source: str) -> list[dict[str, Any]]:
    parsed = parse_hive_lines(text)
    return [
        build_record(packet=packet, line_number=line_number, packet_index=index, source=source)
        for index, (line_number, packet) in enumerate(parsed)
    ]


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def write_manifest(path: Path, *, source: str, out_path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    manifest = {
        "schema": "info_geometry.hive_memory_manifest.v1",
        "source": source,
        "record_count": len(records),
        "artifact_kinds": [record["artifact_kind"] for record in records],
        "out_path": str(out_path),
        "packet_sha256": [record["packet_sha256"] for record in records],
    }
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def read_input(path: Path | None) -> str:
    if path is None:
        return sys.stdin.read()
    return path.read_text(encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="Optional input log file. Reads stdin when omitted.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT, help="Destination JSONL path.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST, help="Destination manifest JSON path.")
    parser.add_argument("--source", default="stdin", help="Source label stored in ingested records.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        text = read_input(args.input)
        records = ingest_text(text, source=str(args.source))
    except HiveIngestError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    write_jsonl(args.out, records)
    write_manifest(args.manifest, source=str(args.source), out_path=args.out, records=records)
    print(f"ingested {len(records)} HIVE_JSON packet(s) to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
