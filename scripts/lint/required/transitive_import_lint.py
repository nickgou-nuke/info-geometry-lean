#!/usr/bin/env python3
"""Check the reachable Lean import closure for missing source modules."""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")


def source_for(module: str) -> Path | None:
    rel = Path(*module.split("."))
    candidates = [ROOT / "src" / rel.with_suffix(".lean"), ROOT / "lean" / rel.with_suffix(".lean")]
    for package in (ROOT / ".lake/packages").glob("*"):
        candidates.extend((package / rel.with_suffix(".lean"), package / rel / "Basic.lean"))
    return next((p for p in candidates if p.is_file()), None)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("files", nargs="*")
    ap.add_argument("--all", action="store_true")
    ns = ap.parse_args()
    if ns.files:
        seeds = [Path(p) if Path(p).is_absolute() else ROOT / p for p in ns.files]
    elif ns.all:
        seeds = [*(ROOT / "src").rglob("*.lean")] if (ROOT / "src").is_dir() else []
        if (ROOT / "lean").is_dir():
            seeds.extend((ROOT / "lean").rglob("*.lean"))
    else:
        diff = subprocess.run(["git", "diff", "--name-only", "--diff-filter=ACMRTUXB", "HEAD", "--", "src", "lean"], cwd=ROOT, text=True, capture_output=True, check=True)
        seeds = [ROOT / p for p in diff.stdout.splitlines() if p.endswith(".lean")]
    pending = [p for p in seeds if p.is_file()]
    visited: set[Path] = set()
    errors: list[str] = []
    while pending:
        path = pending.pop()
        path = path.resolve()
        if path in visited:
            continue
        visited.add(path)
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError) as exc:
            errors.append(f"{path}: cannot read: {exc}")
            continue
        for line_no, line in enumerate(lines, 1):
            match = IMPORT.match(line)
            if not match:
                continue
            module = match.group(1)
            if module == "Mathlib" or module == "Batteries" or module == "Plausible":
                continue
            imported = source_for(module)
            if imported is None:
                if module.startswith(("InfoGeometry.", "DAG.", "Agent.")):
                    errors.append(f"{path.relative_to(ROOT)}:{line_no}: unresolved transitive import `{module}`")
            elif (
                imported.is_relative_to(ROOT / "src")
                or imported.is_relative_to(ROOT / "lean")
                or imported.is_relative_to(ROOT / ".lake/packages")
            ):
                pending.append(imported)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"transitive import closure: passed ({len(visited)} source modules visited)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
