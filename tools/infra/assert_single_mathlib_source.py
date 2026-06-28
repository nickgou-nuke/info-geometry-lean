#!/usr/bin/env python3
"""Reject mixed mathlib/Qq/Plausible sources in the active build configs.

This guard is intentionally narrow: it checks the repo-owned build surfaces
that participate in the active Lake graph and refuses to proceed if any of
them still point at upstream git sources for mathlib, Qq, or Plausible.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

CONFIG_PATHS = [
    ROOT / "lakefile.lean",
    ROOT / "lake-manifest.json",
    ROOT / "lean_sandbox" / "lakefile.lean",
    ROOT / "lib" / "InfoGeometryCore" / "lakefile.toml",
    ROOT / "lib" / "InfoGeometryCore" / "lake-manifest.json",
    ROOT / "pure_math_lib" / "lakefile.toml",
    ROOT / ".lake" / "packages" / "Paperproof" / "lakefile.lean",
    ROOT / ".lake" / "packages" / "LeanArchitect" / "lakefile.lean",
    ROOT / ".lake" / "packages" / "LeanArchitect" / "lake-manifest.json",
    ROOT / ".lake" / "packages" / "doc-gen4" / "lakefile.lean",
    ROOT / ".lake" / "packages" / "doc-gen4" / "lake-manifest.json",
    ROOT / "external_refs" / "gift-framework-core" / "lakefile.lean",
    ROOT / "external_refs" / "gift-framework-core" / "lake-manifest.json",
    ROOT / "external_refs" / "atlas-lean" / "lakefile.toml",
]

FORBIDDEN_PATTERNS = {
    "mathlib": re.compile(r"mathlib4\.git|require\s+mathlib\s+from\s+git|name\s*=\s*\"mathlib\".*\btype\s*=\s*\"git\"", re.S),
    "Qq": re.compile(r"quote4\.git|require\s+Qq\s+from\s+git|require\s+\"leanprover-community\"\s*/\s*\"Qq\"\s*@\s*git|name\s*=\s*\"Qq\".*\btype\s*=\s*\"git\"", re.S),
    "Plausible": re.compile(r"plausible\.git|require\s+plausible\s+from\s+git|require\s+Plausible\s+from\s+git|name\s*=\s*\"Plausible\".*\btype\s*=\s*\"git\"|name\s*=\s*\"plausible\".*\btype\s*=\s*\"git\"", re.S),
}


def check_text(path: Path) -> list[str]:
    if not path.exists():
        return [f"{path}: missing"]
    text = path.read_text(encoding="utf-8")
    problems: list[str] = []
    for name, pat in FORBIDDEN_PATTERNS.items():
        if pat.search(text):
            problems.append(f"{path}: forbidden upstream {name} source/pin detected")
    return problems


def check_manifest(path: Path) -> list[str]:
    if not path.exists():
        return [f"{path}: missing"]
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return [f"{path}: invalid JSON: {e}"]
    packages = data.get("packages", [])
    problems: list[str] = []
    for pkg in packages:
        name = pkg.get("name")
        if name in {"mathlib", "Qq", "Plausible", "plausible"} and pkg.get("type") != "path":
            problems.append(f"{path}: package `{name}` is not a path package")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.parse_args()

    problems: list[str] = []
    for path in CONFIG_PATHS:
        if path.suffix == ".json":
            problems.extend(check_manifest(path))
        else:
            problems.extend(check_text(path))

    if problems:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        return 1

    print("single-mathlib-source preflight: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
