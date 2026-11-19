#!/usr/bin/env python3
"""Hollow Theorem Detector for Lean Codebases.

Flags theorems/lemmas as `[hollow]` when they contain `sorry`/`admit`, prove
`: True` via `trivial`/`True.intro`, or close solely with `by assumption`, and
emits non-blocking `[hollow-advisory]` hints for trivial `abs_nonneg` wrappers.

Usage: python3 tools/quality/detect_hollow_theorems.py [--strict] <path>...
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.quality.audit_constructivity import strip_comments
else:
    from tools.quality.audit_constructivity import strip_comments

_DECL_START_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|strict_theorem)\s+([A-Za-z0-9_'.«»]+)"
)
_BOUNDARY_RE = re.compile(
    r"^(?:@\[|(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|strict_theorem|def|abbrev|example|structure|class|inductive|instance|axiom|opaque)\b|"
    r"(?:namespace|section|end|open|variable|universe|attribute|set_option|#)\b)"
)
_SKIP_DIRS = {".lake", ".lake-packages", "lake-packages", ".git", ".agents"}
_SORRY_ADMIT_RE = re.compile(r"\b(?:sorry|admit)\b")
_TRIVIAL_TRUE_BODY_RE = re.compile(r"^\s*(?:by\s+)?(?:exact\s+)?(?:trivial|True\.intro)\s*$")
_BY_ASSUMPTION_RE = re.compile(r"^\s*by\s+assumption\s*$")
_ABS_NONNEG_RE = re.compile(r"^\s*(?:by\s+)?(?:exact\s+)?abs_nonneg\b[^\n;]*$")


def _split_top_level_assign(decl_text: str) -> tuple[str, str]:
    """Split a declaration slice at the first top-level `:=`."""
    depth = 0
    n = len(decl_text)
    i = 0
    while i < n:
        ch = decl_text[i]
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth = max(0, depth - 1)
        elif depth == 0 and decl_text.startswith(":=", i):
            return decl_text[:i], decl_text[i + 2 :]
        i += 1
    return decl_text, ""


def _top_level_result_is_true(header: str) -> bool:
    """Return True iff the declaration's top-level result type after `:` is `True`."""
    depth = 0
    colon_idx: int | None = None
    for idx, ch in enumerate(header):
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth = max(0, depth - 1)
        elif depth == 0 and ch == ":":
            colon_idx = idx
            break
    if colon_idx is None:
        return False
    return header[colon_idx + 1 :].strip() == "True"


def _has_simp_attr(lines: list[str], decl_idx: int) -> bool:
    """Check declaration line and contiguous preceding attribute lines for `simp`."""
    if "@[" in lines[decl_idx] and re.search(r"\bsimp\b", lines[decl_idx]):
        return True
    for j in range(decl_idx - 1, max(-1, decl_idx - 4), -1):
        stripped = lines[j].strip()
        if not stripped:
            continue
        if stripped.startswith("@[") and not _DECL_START_RE.match(stripped):
            if re.search(r"\bsimp\b", stripped):
                return True
            continue
        break
    return False


def scan_lean_file(path: Path) -> list[tuple[str, int, str]]:
    """Scan one `.lean` file and return `(decl_name, line_no, tag)` tuples."""
    text = path.read_text(encoding="utf-8", errors="ignore")
    clean = strip_comments(text, strip_strings=True)
    lines = clean.splitlines()
    results: list[tuple[str, int, str]] = []
    i = 0
    n = len(lines)
    while i < n:
        m = _DECL_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(2)
        start = i
        j = i + 1
        while j < n and not _BOUNDARY_RE.match(lines[j]):
            j += 1
        decl_text = "\n".join(lines[start:j])
        header, rhs = _split_top_level_assign(decl_text)
        rhs_stripped = rhs.strip()
        body = rhs_stripped if rhs_stripped else decl_text
        if (
            _SORRY_ADMIT_RE.search(body)
            or (_top_level_result_is_true(header) and _TRIVIAL_TRUE_BODY_RE.match(rhs_stripped))
            or _BY_ASSUMPTION_RE.match(rhs_stripped)
        ):
            results.append((name, start + 1, "hollow"))
        elif not _has_simp_attr(lines, start) and _ABS_NONNEG_RE.match(rhs_stripped):
            results.append((name, start + 1, "hollow-advisory"))
        i = j
    return results


def iter_lean_targets(paths: list[str]) -> tuple[list[Path], list[str]]:
    """Expand explicit file/directory targets into sorted `.lean` files."""
    files: set[Path] = set()
    missing: list[str] = []
    for raw in paths:
        target = Path(raw)
        if not target.exists():
            missing.append(raw)
            continue
        if target.is_file():
            if target.suffix == ".lean":
                files.add(target)
        elif target.is_dir():
            for lean_file in target.rglob("*.lean"):
                if lean_file.is_file() and not any(part in _SKIP_DIRS for part in lean_file.parts):
                    files.add(lean_file)
    return sorted(files), missing


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Detect hollow or sorry-bearing Lean theorems.")
    parser.add_argument("paths", nargs="+", help="Lean files or directories to scan.")
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit non-zero if any blocking `[hollow]` finding or missing target is detected.",
    )
    args = parser.parse_args(argv)

    lean_files, missing = iter_lean_targets(args.paths)
    for bad in missing:
        print(f"detect_hollow_theorems: target not found: {bad}", file=sys.stderr)

    blocking_found = False
    for lean_file in lean_files:
        for name, lineno, tag in scan_lean_file(lean_file):
            print(f"{lean_file}:{lineno}: {name} [{tag}]")
            if tag == "hollow":
                blocking_found = True

    if missing and args.strict:
        return 2
    if args.strict and blocking_found:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
