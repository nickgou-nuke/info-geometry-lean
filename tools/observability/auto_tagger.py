#!/usr/bin/env python3
"""Repo-native auto-tagger for owner-target contracts.

This tool is intentionally narrow:

* `def ...OwnerTarget : Prop` gets `@[owner_target_tag]`.
For owner-target defs, any nearby `rep_depth` attribute is removed. In this
repo, owner-target contracts are plain tagged `Prop` defs.

The script can run in dry-run mode and only writes files when `--write` is set.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Tuple

OWNER_IMPORT = "import InfoGeometry.Meta.OwnerTarget"

OWNER_DEF_RE = re.compile(r"^(\s*)def\s+([A-Za-z0-9_']*OwnerTarget[A-Za-z0-9_']*)\s*:\s*Prop\b")
ATTR_RE = re.compile(r"^\s*@\[(.*)\]\s*$")
REP_DEPTH_RE = re.compile(r"^\s*rep_depth\s+(.+?)\s*$")
REP_DEPTH_ANY_RE = re.compile(r"\brep_depth\s+(.+)$")


@dataclass
class FilePlan:
    path: Path
    modified: bool
    owner_hits: int
    imports_added: list[str]


def iter_lean_files(root: Path) -> Iterable[Path]:
    for path in sorted(root.rglob("*.lean")):
        yield path


def build_block_comment_mask(lines: list[str]) -> list[bool]:
    """Mark lines that are inside a Lean block comment.

    This is intentionally lightweight: it is good enough to avoid matching
    docstring examples and other fenced snippets while keeping the scanner
    fast and local.
    """
    mask: list[bool] = []
    depth = 0
    for line in lines:
        mask.append(depth > 0 or line.lstrip().startswith("--"))
        i = 0
        while i < len(line):
            if i + 1 < len(line) and line[i] == "/" and line[i + 1] == "-":
                depth += 1
                i += 2
                continue
            if i + 1 < len(line) and line[i] == "-" and line[i + 1] == "/":
                depth = max(0, depth - 1)
                i += 2
                continue
            i += 1
    return mask


def attr_stack_bounds(lines: list[str], decl_idx: int) -> Tuple[int, int]:
    start = decl_idx
    while start > 0 and lines[start - 1].lstrip().startswith("@["):
        start -= 1
    return start, decl_idx


def parse_attr_body(line: str) -> str | None:
    m = ATTR_RE.match(line)
    if not m:
        return None
    return m.group(1).strip()


def rep_depth_expr(attr_body: str) -> str | None:
    m = REP_DEPTH_RE.match(attr_body)
    if m:
        return m.group(1).strip()
    return None


def rep_depth_expr_any(attr_body: str) -> str | None:
    m = REP_DEPTH_ANY_RE.search(attr_body)
    if m:
        return m.group(1).strip()
    return None


def normalize_owner_stack(stack: list[str]) -> list[str]:
    """Return a normalized owner-target attribute stack."""
    normalized: list[str] = ["@[owner_target_tag]\n"]
    for line in stack:
        body = parse_attr_body(line)
        if body is None:
            normalized.append(line)
            continue
        if "owner_target_tag" in body or body.startswith("rep_depth "):
            continue
        normalized.append(line)
    return normalized


def replace_stack(lines: list[str], start: int, end: int, new_stack: list[str]) -> None:
    lines[start:end] = new_stack


def ensure_import(lines: list[str], import_stmt: str) -> bool:
    if any(import_stmt in line for line in lines):
        return False
    last_import = -1
    for i, line in enumerate(lines):
        if line.startswith("import "):
            last_import = i
    if last_import >= 0:
        lines.insert(last_import + 1, import_stmt + "\n")
    else:
        lines.insert(0, import_stmt + "\n")
    return True


def process_file(
    path: Path,
    dry_run: bool = False,
    owner_import: str = OWNER_IMPORT,
) -> FilePlan:
    lines = path.read_text().splitlines(keepends=True)
    comment_mask = build_block_comment_mask(lines)
    modified = False
    owner_hits = 0
    need_owner_import = False

    i = 0
    while i < len(lines):
        line = lines[i]

        if comment_mask[i]:
            i += 1
            continue

        owner_match = OWNER_DEF_RE.match(line)
        if owner_match:
            need_owner_import = True
            start, end = attr_stack_bounds(lines, i)
            new_stack = normalize_owner_stack(lines[start:end])
            if new_stack != lines[start:end]:
                replace_stack(lines, start, end, new_stack)
                modified = True
                owner_hits += 1
                i = start + len(new_stack)
                continue
            i += 1
            continue

        i += 1

    imports_added: list[str] = []
    if need_owner_import and ensure_import(lines, owner_import):
        imports_added.append(owner_import)
        modified = True
    if modified:
        if not dry_run:
            path.write_text("".join(lines))

    return FilePlan(
        path=path,
        modified=modified,
        owner_hits=owner_hits,
        imports_added=imports_added,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default="lean/InfoGeometry",
        help="Root directory to scan (default: lean/InfoGeometry)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Report planned edits without writing files",
    )
    parser.add_argument(
        "--owner-import",
        default=OWNER_IMPORT,
        help="Owner-target import to inject when needed",
    )
    args = parser.parse_args()

    root = Path(args.root)
    plans = [
        process_file(
            path,
            dry_run=args.dry_run,
            owner_import=args.owner_import,
        )
        for path in iter_lean_files(root)
    ]

    modified = [p for p in plans if p.modified]
    owner_total = sum(p.owner_hits for p in plans)

    mode = "dry-run" if args.dry_run else "write"
    print(f"auto_tagger[{mode}]: scanned {len(plans)} files")
    print(f"auto_tagger[{mode}]: owner hits={owner_total}")
    print(f"auto_tagger[{mode}]: modified files={len(modified)}")

    if modified:
        for plan in modified[:50]:
            imports = ", ".join(plan.imports_added) if plan.imports_added else "-"
            print(
                f"  {plan.path}: owner={plan.owner_hits} imports={imports}"
            )
        if len(modified) > 50:
            print(f"  ... {len(modified) - 50} more")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
