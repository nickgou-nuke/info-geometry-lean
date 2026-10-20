#!/usr/bin/env python3
"""Validate the checked-in ChatGPT-share extraction without treating prose as proof."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def labels(text: str, pattern: str) -> list[int]:
    return [int(value) for value in re.findall(pattern, text, flags=re.MULTILINE)]


def contiguous(values: list[int], expected: int) -> bool:
    return len(values) == expected and sorted(values) == list(range(expected)) and len(set(values)) == expected


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=Path("docs/CHATGPT_SHARE_PLABIC_KREIN_REPRODUCIBILITY.json"))
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    root = args.manifest.parent.parent
    extraction = root / manifest["local_artifacts"]["transcript_extraction"]
    poset = root / manifest["local_artifacts"]["archetype_poset"]
    if not extraction.is_file() or not poset.is_file():
        fail("declared extraction artifacts are missing")
    extraction_text = extraction.read_text(encoding="utf-8")
    poset_text = poset.read_text(encoding="utf-8")
    prompts = labels(extraction_text, r"^### P(\d+)\b")
    c_rows = labels(extraction_text, r"^\| C(\d+) \|")
    a_rows = labels(poset_text, r"^\| A(\d+) \|")
    if not contiguous(prompts, 44):
        fail(f"prompt labels are not exactly P00-P43: {prompts}")
    if not contiguous(c_rows, 18):
        fail(f"C rows are not exactly C0-C17: {c_rows}")
    if not contiguous(a_rows, 28):
        fail(f"A rows are not exactly A0-A27: {a_rows}")
    reported = manifest["source_hashes"]
    for relative, expected in reported.items():
        actual = sha256(root / relative)
        if actual != expected:
            fail(f"hash mismatch for {relative}: {actual} != {expected}")
    raw = manifest["raw_payload"]
    if raw["status"] != "unavailable_in_checkout" or raw["path"] is not None or raw["sha256"] is not None:
        fail("raw payload metadata must explicitly remain unavailable")
    if manifest["live_url_verification"]["status"] == "verified" and raw["sha256"] is None:
        fail("live verification cannot be claimed without a raw payload hash")
    print(json.dumps({
        "status": "ok",
        "prompt_windows": len(prompts),
        "archetype_rows": len(c_rows),
        "directed_archetype_rows": len(a_rows),
        "hashes_checked": len(reported),
        "raw_payload": raw["status"],
        "live_url_verification": manifest["live_url_verification"]["status"],
    }, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
