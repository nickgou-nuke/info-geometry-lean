#!/usr/bin/env python3
"""Assert the Lean toolchain freeze used by this repository."""
from __future__ import annotations

from pathlib import Path
import json
import subprocess
import sys

EXPECTED = "leanprover/lean4:v4.28.1"
EXPECTED_MATHLIB_REV = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
EXPECTED_PACKAGE_REVISIONS = {
    "mathlib": EXPECTED_MATHLIB_REV,
    "Qq": "b8f98e9087e02c8553945a2c5abf07cec8e798c3",
    "plausible": "55c8532eb21ec9f6d565d51d96b8ca50bd1fbef3",
}
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
    mathlib = ROOT / ".lake" / "packages" / "mathlib"
    if mathlib.exists() and (mathlib / ".git").exists():
        head = subprocess.run(
            ["git", "-C", str(mathlib), "rev-parse", "HEAD"],
            check=False, capture_output=True, text=True,
        ).stdout.strip()
        if head != EXPECTED_MATHLIB_REV:
            print(f"FAIL {mathlib}: HEAD {head!r} != {EXPECTED_MATHLIB_REV!r}")
            ok = False
        else:
            print(f"OK {mathlib}: pinned {head}")
    manifest = ROOT / "lake-manifest.json"
    if manifest.exists():
        packages = json.loads(manifest.read_text(encoding="utf-8")).get("packages", [])
        for package in packages:
            name = package.get("name")
            revision = package.get("rev")
            if name in EXPECTED_PACKAGE_REVISIONS and revision != EXPECTED_PACKAGE_REVISIONS[name]:
                print(f"FAIL manifest {name}: {revision!r} != {EXPECTED_PACKAGE_REVISIONS[name]!r}")
                ok = False
            package_dir_name = str(name).replace("«", "").replace("»", "")
            package_dir = ROOT / ".lake" / "packages" / package_dir_name
            package_toolchain = package_dir / "lean-toolchain"
            if package_toolchain.exists() and package_toolchain.read_text(encoding="utf-8").strip() != EXPECTED:
                print(f"FAIL {package_toolchain}: not {EXPECTED}")
                ok = False
            if package.get("type") == "git" and revision:
                package_git = package_dir / ".git"
                if package_git.exists():
                    actual_revision = subprocess.run(
                        ["git", "-C", str(package_dir), "rev-parse", "HEAD"],
                        check=False, capture_output=True, text=True,
                    ).stdout.strip()
                    if actual_revision != revision:
                        print(
                            f"FAIL {package_dir}: HEAD {actual_revision!r} != manifest {revision!r}"
                        )
                        ok = False
                else:
                    print(f"FAIL {package_dir}: git checkout missing")
                    ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
