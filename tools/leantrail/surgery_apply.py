#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
from collections import defaultdict
from pathlib import Path
from typing import Any


class SurgeryApplyError(Exception):
    pass


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return f"sha256:{h.hexdigest()}"


def iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for line_no, raw in enumerate(handle, start=1):
            s = raw.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except Exception as exc:
                raise SurgeryApplyError(f"Invalid JSON at {path}:{line_no}: {exc}") from exc
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")


def nested(obj: dict[str, Any], dotted: str, default: Any = None) -> Any:
    cur: Any = obj
    for part in dotted.split("."):
        if not isinstance(cur, dict):
            return default
        cur = cur.get(part)
    return cur if cur is not None else default


def is_mathlib_owner_module(module: str) -> bool:
    module = str(module).strip()
    return module == "Mathlib" or module.startswith("Mathlib.")


def packet_to_patch(packet: dict[str, Any], repo_root: Path) -> dict[str, Any] | None:
    if packet.get("packet_stream") != "vacuum" or packet.get("action_phase") != "contract":
        return None
    if packet.get("state") not in {"certified", "shadow_approved"}:
        return None
    if packet.get("decl_span_kind") != "top_level_decl":
        return None
    if packet.get("patch_span_kind") != "decl_body":
        return None
    if packet.get("source_info_kind") != "original":
        return None
    payload = packet.get("payload", {}) if isinstance(packet.get("payload", {}), dict) else {}
    sp = payload.get("source_patch", {}) if isinstance(payload.get("source_patch", {}), dict) else {}
    replacement_module = str(payload.get("replacement_module") or packet.get("replacement_module") or "").strip()
    if packet.get("state") == "certified" and not is_mathlib_owner_module(replacement_module):
        raise SurgeryApplyError(
            f"Packet {packet.get('packet_id')} is certified but replacement is not a Mathlib owner module"
        )
    file_raw = packet.get("file") or sp.get("file")
    if not file_raw:
        raise SurgeryApplyError(f"Packet {packet.get('packet_id')} has no file path")
    file_path = Path(str(file_raw))
    if not file_path.is_absolute():
        file_path = (repo_root / file_path).resolve()
    start = sp.get("startByte", sp.get("start_byte"))
    end = sp.get("endByte", sp.get("end_byte"))
    if not isinstance(start, int) or not isinstance(end, int):
        raise SurgeryApplyError(f"Packet {packet.get('packet_id')} lacks integer startByte/endByte")
    replacement = payload.get("replacement_body") or sp.get("replacementText") or sp.get("replacement_text")
    if replacement is None:
        raise SurgeryApplyError(f"Packet {packet.get('packet_id')} lacks replacement text")
    expected_hash = sp.get("fileHash") or sp.get("file_hash") or packet.get("file_hash")
    if not expected_hash:
        raise SurgeryApplyError(f"Packet {packet.get('packet_id')} lacks fileHash/source file hash")
    return {
        "packet_id": packet.get("packet_id", ""),
        "target": packet.get("target", ""),
        "file": str(file_path),
        "startByte": int(start),
        "endByte": int(end),
        "replacementText": str(replacement),
        "fileHash": str(expected_hash),
    }


def validate_non_overlapping(patches: list[dict[str, Any]]) -> None:
    by_file: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
    for p in patches:
        by_file[p["file"]].append((p["startByte"], p["endByte"], p.get("packet_id", "")))
    for file_path, spans in by_file.items():
        spans.sort()
        for (a0, a1, aid), (b0, b1, bid) in zip(spans, spans[1:]):
            if a1 > b0:
                raise SurgeryApplyError(f"Overlapping patches in {file_path}: {aid} {a0}..{a1} overlaps {bid} {b0}..{b1}")


def verify_hashes(patches: list[dict[str, Any]]) -> None:
    expected_by_file: dict[str, str] = {}
    for p in patches:
        file_path = p["file"]
        expected = p["fileHash"]
        existing = expected_by_file.get(file_path)
        if existing is not None and existing != expected:
            raise SurgeryApplyError(f"Conflicting expected hashes for {file_path}: {existing} vs {expected}")
        expected_by_file[file_path] = expected
    for file_path, expected in expected_by_file.items():
        path = Path(file_path)
        if not path.exists():
            raise SurgeryApplyError(f"File not found: {path}")
        actual = sha256_file(path)
        if actual != expected:
            raise SurgeryApplyError(f"FileHash mismatch on {path}: expected {expected}, got {actual}")


def apply_patches_binary(patches: list[dict[str, Any]], *, dry_run: bool = False) -> list[str]:
    validate_non_overlapping(patches)
    verify_hashes(patches)
    by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for p in patches:
        by_file[p["file"]].append(p)
    touched: list[str] = []
    for file_path, fps in by_file.items():
        fps.sort(key=lambda p: int(p["startByte"]), reverse=True)
        path = Path(file_path)
        content = bytearray(path.read_bytes())
        for p in fps:
            start = int(p["startByte"])
            end = int(p["endByte"])
            if start < 0 or end > len(content) or start > end:
                raise SurgeryApplyError(f"Patch bounds out of range for {path}: {start}..{end}, len={len(content)}")
            replacement = str(p["replacementText"]).encode("utf-8")
            content[start:end] = replacement
        if not dry_run:
            path.write_bytes(bytes(content))
        touched.append(file_path)
    return touched


def local_lake_check(repo_root: Path, file_path: str, timeout: int) -> tuple[bool, str]:
    rel_or_abs = str(Path(file_path))
    try:
        result = subprocess.run(
            ["lake", "env", "lean", rel_or_abs],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode == 0, (result.stdout + "\n" + result.stderr).strip()
    except subprocess.TimeoutExpired as exc:
        return False, f"local check timed out after {timeout}s: {exc}"
    except Exception as exc:
        return False, f"local check failed to execute: {exc}"


def run_global_build(repo_root: Path, timeout: int) -> tuple[bool, str]:
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode == 0, (result.stdout + "\n" + result.stderr).strip()
    except subprocess.TimeoutExpired as exc:
        return False, f"global build timed out after {timeout}s: {exc}"
    except Exception as exc:
        return False, f"global build failed to execute: {exc}"


def execute(packet_file: Path, repo_root: Path, *, max_packets: int, dry_run: bool, local_timeout: int, global_build: bool, global_timeout: int) -> dict[str, Any]:
    packets = iter_jsonl(packet_file)
    selected_packets = [p for p in packets if p.get("state") in {"certified", "shadow_approved"}]
    if max_packets > 0:
        selected_packets = selected_packets[:max_packets]
    patches: list[dict[str, Any]] = []
    skipped: list[dict[str, str]] = []
    for p in selected_packets:
        try:
            patch = packet_to_patch(p, repo_root)
            if patch is None:
                skipped.append({"packet_id": str(p.get("packet_id", "")), "reason": "not_applicable"})
            else:
                patches.append(patch)
        except Exception as exc:
            skipped.append({"packet_id": str(p.get("packet_id", "")), "reason": str(exc)})
    backups: dict[str, bytes] = {}
    for path in {p["file"] for p in patches}:
        backups[path] = Path(path).read_bytes()
    try:
        touched = apply_patches_binary(patches, dry_run=dry_run)
    except Exception as exc:
        return {"status": "rejected", "failure_type": "patch_application_error", "reason": str(exc), "skipped": skipped}
    if dry_run:
        return {"status": "dry_run_ok", "patch_count": len(patches), "touched_files": touched, "skipped": skipped}
    local_results: list[dict[str, Any]] = []
    for path in touched:
        ok, output = local_lake_check(repo_root, path, local_timeout)
        local_results.append({"file": path, "ok": ok, "output_tail": output[-4000:]})
        if not ok:
            for bpath, data in backups.items():
                Path(bpath).write_bytes(data)
            return {
                "status": "rejected",
                "failure_type": "local_lake_check_failed",
                "failed_file": path,
                "local_results": local_results,
                "skipped": skipped,
            }
    global_result: dict[str, Any] | None = None
    if global_build:
        ok, output = run_global_build(repo_root, global_timeout)
        global_result = {"ok": ok, "output_tail": output[-6000:]}
        if not ok:
            for bpath, data in backups.items():
                Path(bpath).write_bytes(data)
            return {
                "status": "rejected",
                "failure_type": "global_lake_build_failed",
                "local_results": local_results,
                "global_result": global_result,
                "skipped": skipped,
            }
    return {
        "status": "applied",
        "patch_count": len(patches),
        "touched_files": touched,
        "local_results": local_results,
        "global_result": global_result,
        "skipped": skipped,
        "next_gate": "audit_refresh",
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Apply LeanTrail v1.2 contraction packets with reverse-byte binary splicing.")
    p.add_argument("--packets", default="artifacts/leantrail/vacuum_packets.jsonl")
    p.add_argument("--repo-root", default=".")
    p.add_argument("--max-packets", type=int, default=1)
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("--local-timeout", type=int, default=60)
    p.add_argument("--global-build", action="store_true")
    p.add_argument("--global-timeout", type=int, default=1800)
    p.add_argument("--json-out", default="artifacts/leantrail/surgery_apply_report.json")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(args.repo_root).resolve()
    report = execute(
        Path(args.packets).resolve(),
        repo_root,
        max_packets=int(args.max_packets),
        dry_run=bool(args.dry_run),
        local_timeout=int(args.local_timeout),
        global_build=bool(args.global_build),
        global_timeout=int(args.global_timeout),
    )
    out = Path(args.json_out).resolve()
    write_json(out, report)
    print(json.dumps(report, indent=2, ensure_ascii=True))
    return 0 if report.get("status") in {"applied", "dry_run_ok"} else 2


if __name__ == "__main__":
    raise SystemExit(main())
