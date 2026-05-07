#!/usr/bin/env python3
"""Append-only local JSONL store for schema-validated Hive packets.

This is the first durable honeycomb cell for the Hive: a local, deterministic,
Arango-free packet ledger.  It validates packets before append, computes a
canonical content hash, keeps appends idempotent by default, and exposes small
read-only lineage queries.
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable
import hashlib

try:
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ModuleNotFoundError:  # pragma: no cover - direct script execution fallback
    ROOT_FALLBACK = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT_FALLBACK))
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

ROOT = Path(__file__).resolve().parents[2]


class StoreError(RuntimeError):
    pass


def load_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise StoreError(f"invalid JSON in {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise StoreError(f"packet must be a JSON object: {path}")
    return data


def canonical_packet(packet: dict[str, Any]) -> dict[str, Any]:
    """Return the packet content used for stable hashing.

    Store-added fields are intentionally excluded so re-appending a packet read
    back from the store yields the same hash.
    """
    return {k: v for k, v in packet.items() if k not in {"packet_hash", "store_appended_at"}}


def canonical_json(packet: dict[str, Any]) -> str:
    return json.dumps(canonical_packet(packet), sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def packet_hash(packet: dict[str, Any]) -> str:
    return "sha256:" + hashlib.sha256(canonical_json(packet).encode("utf-8")).hexdigest()


def validate_or_raise(packet: dict[str, Any]) -> None:
    kind = str(packet.get("kind", "")).strip()
    schema_path = SCHEMA_BY_KIND.get(kind)
    if schema_path is None:
        supported = ", ".join(sorted(SCHEMA_BY_KIND))
        raise StoreError(f"unsupported or missing kind: {kind}; supported kinds: {supported}")
    errors = validate_packet(packet, schema_path, build_store())
    if errors:
        joined = "\n".join(f"- {err}" for err in errors)
        raise StoreError(f"packet failed schema validation ({schema_path.name}):\n{joined}")


def read_store(store: Path) -> list[dict[str, Any]]:
    if not store.exists():
        return []
    records: list[dict[str, Any]] = []
    with store.open("r", encoding="utf-8") as fh:
        for line_no, line in enumerate(fh, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                data = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise StoreError(f"invalid JSONL record at {store}:{line_no}: {exc}") from exc
            if not isinstance(data, dict):
                raise StoreError(f"record at {store}:{line_no} is not an object")
            records.append(data)
    return records


def write_store_atomic(store: Path, records: Iterable[dict[str, Any]]) -> None:
    store.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(store.parent), delete=False) as tmp:
        tmp_path = Path(tmp.name)
        for record in records:
            tmp.write(json.dumps(record, sort_keys=True, ensure_ascii=False, separators=(",", ":")))
            tmp.write("\n")
    shutil.move(str(tmp_path), store)


def append_packet(store: Path, packet: dict[str, Any], allow_duplicate: bool = False) -> tuple[str, str]:
    validate_or_raise(packet)
    digest = packet_hash(packet)
    packet_id = str(packet.get("id", "")).strip()
    if not packet_id:
        raise StoreError("packet id is required")

    records = read_store(store)
    for existing in records:
        existing_hash = existing.get("packet_hash") or packet_hash(existing)
        existing_id = str(existing.get("id", ""))
        if existing_hash == digest and not allow_duplicate:
            return digest, "duplicate_hash_ignored"
        if existing_id == packet_id and existing_hash != digest:
            raise StoreError(f"packet id already exists with different hash: {packet_id}")

    stored = dict(packet)
    stored["packet_hash"] = digest
    records.append(stored)
    write_store_atomic(store, records)
    return digest, "appended"


def normalize_ref(ref: Any) -> str | None:
    if isinstance(ref, str):
        return ref
    if isinstance(ref, dict):
        for key in ("packet_id", "id", "ref", "source_id", "uri"):
            value = ref.get(key)
            if isinstance(value, str) and value:
                return value
    return None


def refs_from(packet: dict[str, Any], fields: tuple[str, ...] = ("parent_refs", "evidence_refs")) -> set[str]:
    refs: set[str] = set()
    for field in fields:
        values = packet.get(field, [])
        if isinstance(values, list):
            for value in values:
                ref = normalize_ref(value)
                if ref:
                    refs.add(ref)
    return refs


def filter_records(records: list[dict[str, Any]], args: argparse.Namespace) -> list[dict[str, Any]]:
    out = records
    if getattr(args, "kind", ""):
        out = [r for r in out if r.get("kind") == args.kind]
    if getattr(args, "authority", ""):
        out = [r for r in out if r.get("authority") == args.authority]
    if getattr(args, "lineage_id", ""):
        out = [r for r in out if r.get("lineage_id") == args.lineage_id]
    if getattr(args, "complex_ref", ""):
        wanted = args.complex_ref
        out = [r for r in out if wanted in set(str(x) for x in r.get("complex_refs", []) if isinstance(x, str))]
    return out


def emit_json(data: Any) -> None:
    print(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False))


def compact_record(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": record.get("id"),
        "kind": record.get("kind"),
        "authority": record.get("authority"),
        "status": record.get("status"),
        "lineage_id": record.get("lineage_id"),
        "packet_hash": record.get("packet_hash") or packet_hash(record),
    }


def records_by_id(records: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {str(r.get("id")): r for r in records if r.get("id")}


def cmd_append(args: argparse.Namespace) -> int:
    try:
        digest, status = append_packet(Path(args.store), load_json(Path(args.packet)), args.allow_duplicate)
    except StoreError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    emit_json({"status": status, "packet_hash": digest, "store": str(args.store)})
    return 0


def cmd_list(args: argparse.Namespace) -> int:
    try:
        records = filter_records(read_store(Path(args.store)), args)
    except StoreError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    emit_json([compact_record(record) for record in records])
    return 0


def cmd_show(args: argparse.Namespace) -> int:
    try:
        by_id = records_by_id(read_store(Path(args.store)))
        record = by_id.get(args.id)
    except StoreError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if record is None:
        print(f"ERROR: packet id not found: {args.id}", file=sys.stderr)
        return 1
    emit_json(record)
    return 0


def cmd_parents(args: argparse.Namespace) -> int:
    try:
        records = read_store(Path(args.store))
        by_id = records_by_id(records)
        record = by_id.get(args.id)
    except StoreError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if record is None:
        print(f"ERROR: packet id not found: {args.id}", file=sys.stderr)
        return 1
    emit_json([compact_record(by_id[ref]) if ref in by_id else {"id": ref, "missing": True} for ref in sorted(refs_from(record))])
    return 0


def cmd_children(args: argparse.Namespace) -> int:
    try:
        records = read_store(Path(args.store))
    except StoreError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    children = [record for record in records if args.id in refs_from(record)]
    emit_json([compact_record(record) for record in children])
    return 0


def cmd_lineage(args: argparse.Namespace) -> int:
    try:
        records = read_store(Path(args.store))
        by_id = records_by_id(records)
    except StoreError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if args.id not in by_id:
        print(f"ERROR: packet id not found: {args.id}", file=sys.stderr)
        return 1

    seen: set[str] = set()
    edges: list[dict[str, str]] = []

    def visit(packet_id: str, depth: int) -> None:
        if depth < 0 or packet_id in seen:
            return
        seen.add(packet_id)
        for parent in sorted(refs_from(by_id[packet_id])):
            edges.append({"from": parent, "to": packet_id})
            if parent in by_id:
                visit(parent, depth - 1)

    visit(args.id, args.depth)
    emit_json({
        "root": args.id,
        "nodes": [compact_record(by_id[node]) for node in sorted(seen) if node in by_id],
        "edges": edges,
    })
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_append = sp.add_parser("append", help="Validate and append a packet JSON file.")
    p_append.add_argument("--store", required=True, help="Path to JSONL packet store.")
    p_append.add_argument("--packet", required=True, help="Path to packet JSON.")
    p_append.add_argument("--allow-duplicate", action="store_true", help="Append even if packet_hash already exists.")

    p_list = sp.add_parser("list", help="List packet summaries.")
    p_list.add_argument("--store", required=True)
    p_list.add_argument("--kind", default="")
    p_list.add_argument("--authority", default="")
    p_list.add_argument("--lineage-id", default="")
    p_list.add_argument("--complex-ref", default="")

    p_show = sp.add_parser("show", help="Show one packet by id.")
    p_show.add_argument("--store", required=True)
    p_show.add_argument("--id", required=True)

    p_parents = sp.add_parser("parents", help="Show parent/evidence refs for one packet.")
    p_parents.add_argument("--store", required=True)
    p_parents.add_argument("--id", required=True)

    p_children = sp.add_parser("children", help="Show packets that reference a packet id.")
    p_children.add_argument("--store", required=True)
    p_children.add_argument("--id", required=True)

    p_lineage = sp.add_parser("lineage", help="Show upstream lineage from parent/evidence refs.")
    p_lineage.add_argument("--store", required=True)
    p_lineage.add_argument("--id", required=True)
    p_lineage.add_argument("--depth", type=int, default=8)
    return p.parse_args()


def main() -> None:
    args = parse_args()
    handlers = {
        "append": cmd_append,
        "list": cmd_list,
        "show": cmd_show,
        "parents": cmd_parents,
        "children": cmd_children,
        "lineage": cmd_lineage,
    }
    raise SystemExit(handlers[args.cmd](args))


if __name__ == "__main__":
    main()
