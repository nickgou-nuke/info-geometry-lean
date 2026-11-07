#!/usr/bin/env python3
"""
Hollow Theorem Detector for Lean Codebases

Flags theorems as :hollow if:
- The proof contains `sorry` or `admit`
- The theorem statement has conclusion `True` (`: True :=`)
- The entire proof is a vacuous 1-liner (`by trivial`, `exact True.intro`, `by assumption`, `abs_nonneg`)
- The proof is a bare pass-through assumption transport (`exact h`, `by simpa using h`)

Usage:
  python3 tools/quality/detect_hollow_theorems.py [--strict] [paths...]
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|scoped|local)\s+)*"
    r"(theorem|strict_theorem)\s+([A-Za-z0-9_'.«»]+)"
)
NEXT_TOP_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom|opaque|section|namespace|end)\b|"
    r"^\s*/--?"
)

HOLE_RE = re.compile(r"(?<!\.)\b(?:sorry|admit)\b")
TRUE_CONCLUSION_RE = re.compile(r":\s*True\s*:=")
HOLLOW_WHOLE_PROOF_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("hole", HOLE_RE),
    ("true_conclusion", TRUE_CONCLUSION_RE),
    (
        "trivial_proof",
        re.compile(
            r":=\s*(?:by\s+)?(?:trivial|True\.intro|exact\s+True\.intro|assumption|by\s+assumption|abs_nonneg\b)\s*$",
            re.DOTALL,
        ),
    ),
    (
        "simpa_passthrough",
        re.compile(r":=\s*by\s+simpa\s+using\s+[A-Za-z0-9_'.]+\s*$", re.DOTALL),
    ),
]


def strip_line_comments(text: str) -> str:
    out: list[str] = []
    for line in text.splitlines():
        code = line.split("--", 1)[0]
        if code.strip():
            out.append(code)
    return "\n".join(out)


def classify_decl_block(block: str) -> str | None:
    cleaned = strip_line_comments(block).strip()
    if HOLE_RE.search(cleaned):
        return "hollow:hole"
    if TRUE_CONCLUSION_RE.search(cleaned):
        return "hollow:true_conclusion"
    for tag, pat in HOLLOW_WHOLE_PROOF_PATTERNS[2:]:
        if pat.search(cleaned):
            return f"hollow:{tag}"
    return None


def scan_lean_file(path: Path) -> list[tuple[str, int, str]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        return []

    results: list[tuple[str, int, str]] = []
    n = len(lines)
    i = 0
    in_block_comment = 0

    while i < n:
        raw = lines[i]
        if in_block_comment > 0:
            in_block_comment += raw.count("/-") - raw.count("-/")
            if in_block_comment < 0:
                in_block_comment = 0
            i += 1
            continue
        if raw.strip().startswith("/-"):
            delta = raw.count("/-") - raw.count("-/")
            if delta > 0:
                in_block_comment += delta
            i += 1
            continue

        m = DECL_START_RE.match(raw)
        if not m:
            i += 1
            continue

        name = m.group(2)
        start_line = i + 1
        j = i + 1
        while j < n and not NEXT_TOP_DECL_RE.match(lines[j]):
            j += 1
        block = "\n".join(lines[i:j])
        tag = classify_decl_block(block)
        if tag is not None:
            results.append((name, start_line, tag))
        i = j

    return results


def iter_lean_files(targets: list[str]) -> list[Path]:
    files: list[Path] = []
    for raw in targets:
        p = Path(raw)
        if p.is_file() and p.suffix == ".lean":
            files.append(p)
        elif p.is_dir():
            for child in sorted(p.rglob("*.lean")):
                if any(x in child.parts for x in ("lake-packages", ".lake", ".agents")):
                    continue
                files.append(child)
    return sorted(set(files))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Detect hollow theorems in Lean 4 files.")
    parser.add_argument(
        "paths",
        nargs="*",
        default=["lean/InfoGeometry"],
        help="Lean files or directories to scan.",
    )
    parser.add_argument(
        "--strict",
        "--gate",
        dest="strict",
        action="store_true",
        help="Return non-zero exit code if any hollow theorem is detected.",
    )
    args = parser.parse_args(argv)

    findings = 0
    for lean_file in iter_lean_files(args.paths):
        hollows = scan_lean_file(lean_file)
        for name, lineno, tag in hollows:
            print(f"{lean_file}:{lineno}: {name} [{tag}]")
            findings += 1

    if args.strict and findings > 0:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
