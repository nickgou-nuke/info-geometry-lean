#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import lean_root, repo_root
else:
    from tools.pathing import lean_root, repo_root


ROOT = repo_root()
DEFAULT_REGISTRY = ROOT / "docs" / "OperatorTheoremTranslationRegistry.md"
TABLE_ROW_RE = re.compile(r"^\|\s*TR-[^|]+\|")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Gate for theorem-translation registry: require canonical registry rows "
            "and proof-anchor declarations on the Lean surface."
        )
    )
    parser.add_argument(
        "--registry",
        default=str(DEFAULT_REGISTRY.relative_to(ROOT)),
        help="Path to translation registry markdown file (default: docs/OperatorTheoremTranslationRegistry.md).",
    )
    parser.add_argument(
        "--required-anchor",
        action="append",
        default=[],
        help=(
            "Required Lean anchor (fully qualified name). May be passed multiple times. "
            "Example: InfoGeometry.Canonical.ModularSuperchargeClosure.theorem_name"
        ),
    )
    parser.add_argument(
        "--lean-dir",
        default=str(lean_root().relative_to(ROOT)),
        help="Lean source directory to scan for required anchors (default: lean).",
    )
    return parser.parse_args()


def read_registry_rows(path: Path) -> list[str]:
    rows: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if TABLE_ROW_RE.match(line):
            rows.append(line)
    return rows


def anchor_in_registry(anchor: str, rows: list[str]) -> bool:
    return any(anchor in row for row in rows)


def anchor_declared(anchor: str, lean_files: list[Path]) -> bool:
    short = anchor.split(".")[-1]
    decl_re = re.compile(rf"^\s*(?:theorem|lemma|def|abbrev)\s+{re.escape(short)}\b")
    for path in lean_files:
        try:
            for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
                if decl_re.match(line):
                    return True
        except Exception:
            continue
    return False


def main() -> int:
    args = parse_args()
    registry_path = (ROOT / args.registry).resolve()
    if not registry_path.exists():
        print(f"[translation-registry] missing registry file: {registry_path}")
        return 1

    rows = read_registry_rows(registry_path)
    if not rows:
        print("[translation-registry] no TR-* rows found in registry table")
        return 1

    lean_dir = (ROOT / args.lean_dir).resolve()
    if not lean_dir.exists():
        print(f"[translation-registry] lean source directory not found: {lean_dir}")
        return 1
    lean_files = sorted(lean_dir.rglob("*.lean"))

    required = args.required_anchor
    if not required:
        print("[translation-registry] warning: no required anchors specified; only registry presence checked")
        print(f"[translation-registry] registry rows: {len(rows)}")
        print("[translation-registry] PASSED")
        return 0

    missing_registry: list[str] = []
    missing_decl: list[str] = []
    for anchor in required:
        if not anchor_in_registry(anchor, rows):
            missing_registry.append(anchor)
        if not anchor_declared(anchor, lean_files):
            missing_decl.append(anchor)

    if missing_registry:
        print("[translation-registry] required anchors missing from registry:")
        for anchor in missing_registry:
            print(f"  - {anchor}")
    if missing_decl:
        print("[translation-registry] required anchors missing on Lean declaration surface:")
        for anchor in missing_decl:
            print(f"  - {anchor}")
    if missing_registry or missing_decl:
        return 1

    print(f"[translation-registry] registry rows: {len(rows)}")
    print(f"[translation-registry] required anchors satisfied: {len(required)}")
    print("[translation-registry] PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
