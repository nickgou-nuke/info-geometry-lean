#!/usr/bin/env python3
"""Check that src/ is an exact, fully selected mirror of the lean/ owners.

Lake compiles each Lean module identity once. The root build uses lean/ as its
canonical source tree; src/ remains a mirrored transition lane. This audit
rejects missing or divergent mirrors and ensures every src identity is selected
by a default library.
"""

from __future__ import annotations

import sys
from pathlib import Path
import argparse
import json


ROOT = Path(__file__).resolve().parents[2]
# Shared module identities intentionally kept outside the root default targets.
# These are opt-in audits/sandboxes rather than missing active owners.
NON_DEFAULT_SHARED_MODULES = {
    "AuditNative",
    "AuditStrict",
    "KaplanskyCliffordBridge",
    "sandbox.PeirceProjectors",
    "sandbox.PinGroupStructures",
    "sandbox.SplitArchetypeDictionary",
    "sandbox.TrifactorHomomorphism",
    "sandbox.TrifactorHomomorphismClean",
    "sandbox.TrifactorHomomorphismComplex",
    "sandbox.TrifactorHomomorphismSuper",
}

if __package__ in (None, ""):
    sys.path.insert(0, str(ROOT))

from tools.infra.audit_default_lean_sources import default_sources


def source_inventory(prefix: str) -> dict[str, Path]:
    result: dict[str, Path] = {}
    source_root = ROOT / prefix
    for path in source_root.rglob("*.lean"):
        if ".lake" in path.parts or not path.is_file():
            continue
        module = path.relative_to(source_root).with_suffix("").as_posix().replace("/", ".")
        result[module] = path
    return result


def audit() -> tuple[dict[str, int], list[str], dict[str, list[str]]]:
    src = source_inventory("src")
    lean = source_inventory("lean")
    src_names, lean_names = set(src), set(lean)
    src_only = src_names - lean_names
    shared = src_names & lean_names
    lean_only = sorted(lean_names - src_names)
    all_divergent = sorted(
        name for name in shared if src[name].read_bytes() != lean[name].read_bytes()
    )
    selected = default_sources(ROOT)
    unselected_shared = sorted(name for name in shared if name not in selected)
    selected_shared = {
        name for name in shared if selected.get(name) in {src[name], lean[name]}
    }
    unselected_src = sorted(src_names - set(selected) - NON_DEFAULT_SHARED_MODULES)
    selected_divergent = sorted(
        name for name in selected_shared
        if selected[name].read_bytes() !=
        (lean[name] if selected[name] == src[name] else src[name]).read_bytes()
    )
    unexpected_unselected_shared = sorted(set(unselected_shared) - NON_DEFAULT_SHARED_MODULES)
    stale_non_default_shared = sorted(NON_DEFAULT_SHARED_MODULES - set(unselected_shared))

    summary = {
        "src_modules": len(src_names),
        "lean_modules": len(lean_names),
        "shared_module_names": len(shared),
        "src_only_modules": len(src_only),
        "shared_divergent_modules_all_trees": len(all_divergent),
        "unselected_shared_modules": len(unselected_shared),
        "lean_only_modules": len(lean_only),
        "default_selected_shared_modules": len(selected_shared),
        "default_selected_shared_divergent_modules": len(selected_divergent),
        "unselected_src_modules": len(unselected_src),
        "unexpected_unselected_shared_modules": len(unexpected_unselected_shared),
        "stale_non_default_shared_modules": len(stale_non_default_shared),
    }
    issues = [
        *(f"shared src/lean module differs: {name}" for name in all_divergent),
        *(f"src-only module has no canonical lean owner: {name}" for name in sorted(src_only)),
        *(f"src module is not selected by a default library: {name}" for name in unselected_src),
        *(f"shared module is unselected without an explicit non-default classification: {name}"
          for name in unexpected_unselected_shared),
        *(f"non-default shared classification is stale: {name}"
          for name in stale_non_default_shared),
    ]
    details = {
        "shared_divergent_modules_all_trees": all_divergent,
        "unselected_shared_modules": unselected_shared,
        "unexpected_unselected_shared_modules": unexpected_unselected_shared,
        "stale_non_default_shared_modules": stale_non_default_shared,
        "lean_only_modules": lean_only,
        "default_selected_shared_divergent_modules": selected_divergent,
        "unselected_src_modules": unselected_src,
    }
    return summary, issues, details


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit the complete inventory as JSON.")
    args = parser.parse_args()
    summary, issues, details = audit()
    if args.json:
        print(json.dumps({"summary": summary, **details}, indent=2, sort_keys=True))
        return int(bool(issues))
    print("Dual Lean source-lane audit:")
    for key, value in summary.items():
        print(f"  {key}: {value}")
    if issues:
        print("Source-lane conflicts (first 50):", file=sys.stderr)
        for issue in issues[:50]:
            print(f"  {issue}", file=sys.stderr)
        if len(issues) > 50:
            print(f"  … and {len(issues) - 50} more", file=sys.stderr)
        return 1
    print("  result: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
