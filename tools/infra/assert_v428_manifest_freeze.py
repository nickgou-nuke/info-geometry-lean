#!/usr/bin/env python3
"""Assert the pinned mathlib revision in the Lake package checkout."""
from __future__ import annotations

from pathlib import Path
import subprocess
import sys

EXPECTED_MATHLIB_HEAD = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
ROOT = Path(__file__).resolve().parents[2]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"


def git_head(path: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def main() -> int:
    if not MATHLIB.exists():
        print(f"MISSING {MATHLIB}")
        return 1
    head = git_head(MATHLIB)
    if head != EXPECTED_MATHLIB_HEAD:
        print(f"FAIL mathlib HEAD: {head!r} != {EXPECTED_MATHLIB_HEAD!r}")
        return 1
    print(f"OK mathlib HEAD: {head}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
