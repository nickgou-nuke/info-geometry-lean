#!/usr/bin/env python3
"""Report InfoGeometry Lean modules not reachable from an import root.

Repository policy is that repo-owned Lean modules under ``lean/InfoGeometry``
are repaired and wired into the provided library surface, not hidden elsewhere.
This tool is intentionally read-only: it reports coverage gaps so repair/import
batches can be planned from concrete module names.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


REPO_LEAN_ROOT = Path("lean")
INFO_GEOMETRY_ROOT = REPO_LEAN_ROOT / "InfoGeometry"


def module_name(path: Path) -> str:
    rel = path.relative_to(REPO_LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


def module_path(module: str) -> Path:
    return REPO_LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")


def discover_modules() -> dict[str, Path]:
    return {
        module_name(path): path
        for path in INFO_GEOMETRY_ROOT.rglob("*.lean")
        if path.is_file()
    }


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        text = path.read_text()
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith("import "):
            continue
        parts = line.split()
        if len(parts) >= 2:
            imports.append(parts[1])
    return imports


def reachable_from(roots: list[str], modules: dict[str, Path]) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = modules.get(mod)
        if path is None:
            local_path = module_path(mod)
            if local_path.exists():
                path = local_path
            else:
                continue
        stack.extend(parse_imports(path))
    return seen


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        action="append",
        default=[],
        help="Import root to check. May be passed more than once.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    args = parser.parse_args()

    roots = args.root or ["InfoGeometry", "InfoGeometry.All"]
    modules = discover_modules()
    reachable = reachable_from(roots, modules)
    covered = set(modules) & reachable
    uncovered = sorted(set(modules) - covered)

    payload = {
        "roots": roots,
        "total_info_geometry_modules": len(modules),
        "covered_repo_modules": len(covered),
        "uncovered_repo_modules": len(uncovered),
        "uncovered": uncovered,
    }

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"roots: {', '.join(roots)}")
        print(f"total InfoGeometry modules: {len(modules)}")
        print(f"covered repo modules: {len(covered)}")
        print(f"uncovered repo modules: {len(uncovered)}")
        for mod in uncovered:
            print(mod)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
