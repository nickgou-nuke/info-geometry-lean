#!/usr/bin/env python3
"""Assert the Lean toolchain freeze used by this repository."""
from __future__ import annotations

from pathlib import Path
import sys

EXPECTED = "leanprover/lean4:v4.28.0"
ROOT = Path(__file__).resolve().parents[2]
PATHS = [
    ROOT / "lean-toolchain",
    ROOT / ".lake" / "packages" / "mathlib" / "lean-toolchain",
]


def main() -> int:
    ok = True
    for path in PATHS:
        if not path.exists():
            print(f"MISSING {path}")
            ok = False
            continue
        value = path.read_text(encoding="utf-8").strip()
        if value != EXPECTED:
            print(f"FAIL {path}: {value!r} != {EXPECTED!r}")
            ok = False
        else:
            print(f"OK {path}: {value}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
