#!/usr/bin/env python3
"""Record a post-repair Lean verification outcome for oracle prompt GEPA."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_EVENTS_DIR = ROOT / "quarantine" / "oracle_prompt_gepa" / "events"


def read_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_lean(path: Path, timeout: int) -> dict[str, Any]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )
    return {
        "cmd": ["lake", "env", "lean", str(path)],
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "success": proc.returncode == 0,
    }


def archive_name(event: dict[str, Any]) -> str:
    profile = str(event.get("prompt_profile") or "builtin")
    theorem = str(event.get("theorem") or "unknown").replace("/", "_").replace(" ", "_")
    result = event.get("aiclaw_result", {}) if isinstance(event.get("aiclaw_result"), dict) else {}
    prompt_hash = result.get("prompt_sha256", "")
    meta = result.get("meta", {})
    if not prompt_hash and isinstance(meta, dict):
        prompt_hash = meta.get("prompt_sha256", "")
    digest_source = json.dumps(event, sort_keys=True, default=str)
    digest = hashlib.sha256(digest_source.encode("utf-8")).hexdigest()[:12]
    if isinstance(prompt_hash, str) and prompt_hash:
        digest = prompt_hash[:12]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    safe_profile = "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in profile)
    safe_theorem = "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in theorem)
    return f"{stamp}_{safe_profile}_{safe_theorem}_{digest}.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event-json", required=True, type=Path,
                        help="Oracle JSON event produced by socratic_clawbot.py --json-out.")
    parser.add_argument("--file", type=Path,
                        help="Lean file to verify. Defaults to the event's file field.")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_EVENTS_DIR)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--in-place", action="store_true",
                        help="Also write the verification result back into --event-json.")
    args = parser.parse_args()

    event_path = args.event_json if args.event_json.is_absolute() else ROOT / args.event_json
    event = read_json(event_path)
    lean_file = args.file or Path(str(event.get("file") or ""))
    if not lean_file.is_absolute():
        lean_file = ROOT / lean_file
    if not lean_file.exists():
        raise FileNotFoundError(lean_file)

    event["verification"] = run_lean(lean_file, args.timeout)
    event["verification"]["recorded_at"] = datetime.now(timezone.utc).isoformat()
    event["verification"]["source_event"] = str(event_path.relative_to(ROOT)) if event_path.is_relative_to(ROOT) else str(event_path)

    if args.in_place:
        write_json(event_path, event)

    out_dir = args.out_dir if args.out_dir.is_absolute() else ROOT / args.out_dir
    out_path = args.out if args.out else out_dir / archive_name(event)
    if not out_path.is_absolute():
        out_path = ROOT / out_path
    write_json(out_path, event)

    print(json.dumps({
        "success": event["verification"]["success"],
        "out": str(out_path.relative_to(ROOT)),
        "cmd": event["verification"]["cmd"],
    }, indent=2, sort_keys=True))
    return 0 if event["verification"]["success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
