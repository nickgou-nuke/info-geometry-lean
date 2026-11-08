#!/usr/bin/env python3
"""Audit canonical `lean/` and isolated `src/` Lake source selection.

The trees may contain duplicate module identities with different contents.
They are compiled by separate Lake configurations and output roots; byte-level
equality is diagnostic information, not a requirement for source selection.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
# This root-level src symlink is an external proof pinned to a different Lean
# toolchain; it remains an explicit opt-in target under repository policy.
NON_DEFAULT_SRC_MODULES = {"PrimitiveSetsAboveX"}


if __package__ in (None, ""):
    sys.path.insert(0, str(ROOT))

from tools.infra.audit_default_lean_sources import default_sources


def source_inventory(root: Path, prefix: str) -> dict[str, Path]:
    result: dict[str, Path] = {}
    source_root = root / prefix
    for path in source_root.rglob("*.lean"):
        if ".lake" in path.parts or not path.is_file():
            continue
        module = path.relative_to(source_root).with_suffix("").as_posix().replace("/", ".")
        result[module] = path
    return result


def src_lane_sources(root: Path) -> dict[str, Path]:
    """Resolve the selected modules from the `SrcLane` Lake glob declarations."""
    config_path = root / "lakefile.src.lean"
    config = config_path.read_text(encoding="utf-8")
    package = re.search(r"package\s+infogeometrySrc\s+where(.*?)(?=^require|^@\[|\Z)", config, re.M | re.S)
    library = re.search(r"@\[default_target\]\s*lean_lib\s+SrcLane\s+where(.*?)(?=^\S|\Z)", config, re.M | re.S)
    if not package or not library:
        raise ValueError("lakefile.src.lean must define package infogeometrySrc and default SrcLane")
    build_dir = re.search(r'buildDir\s*:=\s*"([^"]+)"', package.group(1))
    if not build_dir or build_dir.group(1) != ".lake/src-build":
        raise ValueError("SrcLane must keep artifacts isolated under .lake/src-build")
    src_dir = re.search(r'srcDir\s*:=\s*"([^"]+)"', library.group(1))
    if not src_dir or src_dir.group(1) != "src":
        raise ValueError("SrcLane must use src/ as its source root")
    glob_array = re.search(r"globs\s*:=\s*#\[(.*?)\]", library.group(1), re.S)
    if not glob_array:
        raise ValueError("SrcLane must declare explicit module globs")

    source_root = root / src_dir.group(1)
    selected: dict[str, Path] = {}
    glob_pattern = re.compile(r"\.(andSubmodules|one)\s+`([\w.]+)")
    globs = glob_pattern.findall(glob_array.group(1))
    if not globs:
        raise ValueError("SrcLane has no recognized explicit module globs")
    for kind, module in globs:
        base = source_root.joinpath(*module.split("."))
        if kind == "one":
            selected[module] = base.with_suffix(".lean")
            continue
        root_file = base.with_suffix(".lean")
        if root_file.is_file():
            selected[module] = root_file
        if base.is_dir():
            for path in base.rglob("*.lean"):
                relative = path.relative_to(source_root).with_suffix("")
                name = ".".join(relative.parts)
                selected[name] = path
    return selected


def audit(root: Path) -> tuple[dict[str, int], list[str], dict[str, list[str]]]:
    src = source_inventory(root, "src")
    lean = source_inventory(root, "lean")
    canonical = default_sources(root)
    selected_src = src_lane_sources(root)
    src_names, lean_names = set(src), set(lean)
    selected_src_names = set(selected_src)
    unselected_src = sorted(src_names - selected_src_names - NON_DEFAULT_SRC_MODULES)
    nondefault_src = sorted(src_names & NON_DEFAULT_SRC_MODULES)
    selected_missing = sorted(
        name for name, path in selected_src.items() if not path.is_file()
    )
    shared = src_names & lean_names
    divergent = sorted(
        name for name in shared if src[name].read_bytes() != lean[name].read_bytes()
    )
    canonical_missing = sorted(name for name, path in canonical.items() if not path.is_file())

    summary = {
        "src_modules": len(src_names),
        "lean_modules": len(lean_names),
        "src_lane_selected_modules": len(selected_src_names),
        "src_modules_unselected": len(unselected_src),
        "src_modules_explicitly_non_default": len(nondefault_src),
        "src_selected_paths_missing": len(selected_missing),
        "shared_module_names": len(shared),
        "shared_divergent_modules": len(divergent),
        "src_only_modules": len(src_names - lean_names),
        "lean_only_modules": len(lean_names - src_names),
        "canonical_default_modules": len(canonical),
        "canonical_default_paths_missing": len(canonical_missing),
    }
    issues = [
        *(f"src module is not selected by SrcLane: {name}" for name in unselected_src),
        *(f"SrcLane selects a missing source: {name}" for name in selected_missing),
        *(f"canonical default selects a missing source: {name}" for name in canonical_missing),
    ]
    details = {
        "src_modules_unselected": unselected_src,
        "src_modules_explicitly_non_default": nondefault_src,
        "src_selected_paths_missing": selected_missing,
        "shared_divergent_modules": divergent,
        "src_only_modules": sorted(src_names - lean_names),
        "lean_only_modules": sorted(lean_names - src_names),
        "canonical_default_paths_missing": canonical_missing,
    }
    return summary, issues, details


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit the complete inventory as JSON.")
    args = parser.parse_args()
    summary, issues, details = audit(ROOT)
    if args.json:
        print(json.dumps({"summary": summary, **details}, indent=2, sort_keys=True))
        return int(bool(issues))
    print("Dual Lean source-lane audit:")
    for key, value in summary.items():
        print(f"  {key}: {value}")
    if issues:
        print("Source-lane selection issues (first 50):", file=sys.stderr)
        for issue in issues[:50]:
            print(f"  {issue}", file=sys.stderr)
        if len(issues) > 50:
            print(f"  … and {len(issues) - 50} more", file=sys.stderr)
        return 1
    print("  result: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
