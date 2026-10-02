#!/usr/bin/env python3
"""Assert the Lean toolchain freeze used by this repository."""
from __future__ import annotations

from pathlib import Path
import json
import subprocess
import sys

EXPECTED = "leanprover/lean4:v4.28.1"
EXPECTED_MATHLIB_REV = "1f9fffd5ff0b854b8a1f1f69adc11c61f05f2515"
EXPECTED_PACKAGE_REVISIONS = {
    "mathlib": EXPECTED_MATHLIB_REV,
    "Qq": "b8f98e9087e02c8553945a2c5abf07cec8e798c3",
    "plausible": "55c8532eb21ec9f6d565d51d96b8ca50bd1fbef3",
}
ROOT = Path(__file__).resolve().parents[2]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"


def main() -> int:
    ok = True
    root_toolchain = ROOT / "lean-toolchain"
    if not root_toolchain.exists():
        print(f"MISSING {root_toolchain}")
        ok = False
    else:
        value = root_toolchain.read_text(encoding="utf-8").strip()
        if value != EXPECTED:
            print(f"FAIL {root_toolchain}: {value!r} != {EXPECTED!r}")
            ok = False
        else:
            print(f"OK root toolchain: {value}")

    # The repository and Mathlib are built by the root toolchain. Other Lake
    # dependencies may contain their own upstream lean-toolchain files; those
    # files do not override the compiler selected by this workspace.
    mathlib_toolchain = MATHLIB / "lean-toolchain"
    if mathlib_toolchain.exists():
        value = mathlib_toolchain.read_text(encoding="utf-8").strip()
        if value != EXPECTED:
            print(f"FAIL {mathlib_toolchain}: {value!r} != {EXPECTED!r}")
            ok = False
        else:
            print(f"OK Mathlib toolchain: {value}")
    elif MATHLIB.exists():
        print(f"INFO {mathlib_toolchain} absent; checkout may be incomplete")

    if MATHLIB.exists() and (MATHLIB / ".git").exists():
        head = subprocess.run(
            ["git", "-C", str(MATHLIB), "rev-parse", "HEAD"],
            check=False, capture_output=True, text=True,
        ).stdout.strip()
        if head != EXPECTED_MATHLIB_REV:
            print(f"FAIL {MATHLIB}: HEAD {head!r} != {EXPECTED_MATHLIB_REV!r}")
            ok = False
        else:
            print(f"OK Mathlib revision: {head}")
    elif MATHLIB.exists():
        print(f"FAIL {MATHLIB}: Git checkout metadata missing")
        ok = False
    else:
        print("INFO Mathlib checkout not materialized yet; manifest pins remain authoritative")

    manifest = ROOT / "lake-manifest.json"
    if not manifest.exists():
        print(f"MISSING {manifest}")
        ok = False
    else:
        packages = json.loads(manifest.read_text(encoding="utf-8")).get("packages", [])
        for package in packages:
            name = package.get("name")
            revision = package.get("rev")
            if name in EXPECTED_PACKAGE_REVISIONS and revision != EXPECTED_PACKAGE_REVISIONS[name]:
                print(f"FAIL manifest {name}: {revision!r} != {EXPECTED_PACKAGE_REVISIONS[name]!r}")
                ok = False
            package_dir_name = str(name).replace("«", "").replace("»", "")
            package_dir = ROOT / ".lake" / "packages" / package_dir_name
            if package.get("type") == "git" and revision:
                package_git = package_dir / ".git"
                if not package_dir.exists():
                    print(f"INFO dependency checkout not materialized yet: {name}")
                elif package_git.exists():
                    actual_revision = subprocess.run(
                        ["git", "-C", str(package_dir), "rev-parse", "HEAD"],
                        check=False, capture_output=True, text=True,
                    ).stdout.strip()
                    if actual_revision != revision:
                        print(
                            f"FAIL {package_dir}: HEAD {actual_revision!r} != manifest {revision!r}"
                        )
                        ok = False
                elif package_dir.exists():
                    print(f"FAIL {package_dir}: git checkout missing")
                    ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
