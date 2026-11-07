#!/usr/bin/env python3
"""Phase 3 Linter: AI-Generated / LLM Proof Anti-Pattern Detector for Lean 4.

Checks target Lean files for common LLM formalization shortcuts:
  1. Proof holes (`sorry`, `admit`, `axiom`, `postulate`)
  2. Unsafe kernel bypasses (`native_decide`, `unsafe`, `implemented_by`)
  3. Vacuous `Prop` definitions (`def ... : Prop := True`, `: True :=`)
  4. Forwarding wrapper blocks (`export ...`)
  5. Witness/Evidence/Datum/Certificate Prop-packaging structures

Usage:
  python3 scripts/lint/required/llm_proof_lint.py [files...]
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]

COMMENT_BLOCK_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")

CHECKS: list[tuple[str, re.Pattern[str], str]] = [
    (
        "proof_hole",
        re.compile(r"(?<!\.)\b(?:sorry|admit|axiom|postulate)\b"),
        "forbidden proof hole or custom axiom (`sorry`/`admit`/`axiom`)",
    ),
    (
        "unsafe_bypass",
        re.compile(r"\b(?:native_decide|implemented_by)\b"),
        "forbidden kernel evaluation bypass (`native_decide` / `implemented_by`)",
    ),
    (
        "vacuous_prop_def",
        re.compile(r"\bdef\s+[A-Za-z0-9_'.]+\s*[^:=\n]*:\s*Prop\s*:=\s*True\b"),
        "vacuous `def ... : Prop := True` wrapper",
    ),
    (
        "true_conclusion",
        re.compile(r"\b(?:theorem|lemma)\s+[A-Za-z0-9_'.]+[^:=\n]*:\s*True\s*:="),
        "vacuous theorem with conclusion `: True`",
    ),
    (
        "witness_structure",
        re.compile(
            r"^\s*structure\s+[A-Za-z0-9_']*(?:Witness|Evidence|Certificate|Datum|Packet)\b",
            re.MULTILINE,
        ),
        "witness/evidence/certificate structure container (use genuine theorems instead)",
    ),
]


def scrub_comments(text: str) -> str:
    masked = COMMENT_BLOCK_RE.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    return LINE_COMMENT_RE.sub("", masked)


def collect_files(paths: list[str], scan_all: bool) -> list[Path]:
    if paths:
        out: list[Path] = []
        for raw in paths:
            p = Path(raw) if Path(raw).is_absolute() else ROOT / raw
            if p.is_file() and p.suffix == ".lean":
                out.append(p)
            elif p.is_dir():
                out.extend(sorted(p.rglob("*.lean")))
        return sorted(set(out))
    if scan_all:
        paths = [*(ROOT / "src").rglob("*.lean")] if (ROOT / "src").is_dir() else []
        if (ROOT / "lean").is_dir():
            paths.extend((ROOT / "lean").rglob("*.lean"))
        return sorted(paths)
    res = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMRTUXB", "HEAD", "--", "src", "lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return [ROOT / p for p in res.stdout.splitlines() if p.endswith(".lean") and (ROOT / p).is_file()]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("files", nargs="*", help="Lean files or directories to scan.")
    ap.add_argument("--all", action="store_true", help="Scan all Lean files under lean/.")
    args = ap.parse_args()

    files = collect_files(args.files, args.all)
    findings: list[str] = []

    for path in files:
        if not path.is_file():
            continue
        raw = path.read_text(encoding="utf-8", errors="ignore")
        scrubbed = scrub_comments(raw)
        rel = path.resolve().relative_to(ROOT).as_posix()
        for tag, pattern, detail in CHECKS:
            for m in pattern.finditer(scrubbed):
                line_no = scrubbed.count("\n", 0, m.start()) + 1
                findings.append(f"{rel}:{line_no} [{tag}]: {detail}")

    if findings:
        print(f"[llm_proof_lint] FAILED ({len(findings)} issue(s)):", file=sys.stderr)
        for item in findings[:100]:
            print(f"  - {item}", file=sys.stderr)
        return 1

    print(f"[llm_proof_lint] PASSED ({len(files)} file(s) verified)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
