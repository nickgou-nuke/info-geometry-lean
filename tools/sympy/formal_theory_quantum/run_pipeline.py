#!/usr/bin/env python3
"""Agentic SymPy runner for `formal-theory-quantum.lean`.

The pipeline mirrors the Lean build loop at a lightweight level:

1. scan the Lean file for `chapterN_*` lemma stubs;
2. require a Python companion for each chapter;
3. run companions in order with timeouts;
4. write a machine-readable JSON report;
5. fail nonzero if any companion is missing or fails.

This is a computational shadow pipeline only.  It never marks Lean declarations
as proved and never replaces kernel-checked theorem ownership.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
DEFAULT_LEAN = REPO / "formal-theory-quantum.lean"
DEFAULT_OUT = REPO / "artifacts" / "sympy" / "formal_theory_quantum" / "results.json"
SCRIPT_DIR = Path(__file__).resolve().parent

SCRIPT_BY_CHAPTER = {
    1: "chapter1_quantum_sl2.py",
    2: "chapter2_quasitriangular.py",
    3: "chapter3_yang_baxter.py",
    4: "chapter4_braided_category.py",
    5: "chapter5_roots_of_unity.py",
    6: "chapter6_fibonacci_mtc.py",
    7: "chapter7_explicit_f_and_r.py",
    8: "chapter8_hexagon.py",
}


@dataclass
class ChapterResult:
    chapter: int
    lean_lemma: str
    script: str
    status: str
    returncode: int | None
    stdout: str
    stderr: str


def discover_chapters(lean_file: Path) -> list[tuple[int, str]]:
    text = lean_file.read_text()
    found = []
    for match in re.finditer(r"lemma\s+(chapter(\d+)_[A-Za-z0-9_']+)\s*:", text):
        found.append((int(match.group(2)), match.group(1)))
    return sorted(found)


def run_chapter(chapter: int, lemma: str, timeout: int) -> ChapterResult:
    script_name = SCRIPT_BY_CHAPTER.get(chapter)
    if script_name is None:
        return ChapterResult(chapter, lemma, "", "missing_mapping", None, "", "")
    script = SCRIPT_DIR / script_name
    if not script.exists():
        return ChapterResult(chapter, lemma, str(script), "missing_script", None, "", "")

    proc = subprocess.run(
        [sys.executable, str(script)],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    status = "passed" if proc.returncode == 0 else "failed"
    return ChapterResult(chapter, lemma, str(script.relative_to(REPO)), status, proc.returncode, proc.stdout, proc.stderr)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-file", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()

    chapters = discover_chapters(args.lean_file)
    expected = set(range(1, 9))
    discovered = {chapter for chapter, _ in chapters}
    missing = sorted(expected - discovered)

    results = [run_chapter(chapter, lemma, args.timeout) for chapter, lemma in chapters]
    for chapter in missing:
        results.append(ChapterResult(chapter, "", "", "missing_lean_chapter", None, "", ""))

    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "lean_file": str(args.lean_file),
        "results": [asdict(result) for result in sorted(results, key=lambda item: item.chapter)],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    for result in sorted(results, key=lambda item: item.chapter):
        print(f"chapter {result.chapter}: {result.status} :: {result.lean_lemma or '<missing>'}")
        if result.stdout:
            print(result.stdout.rstrip())
        if result.stderr:
            print(result.stderr.rstrip(), file=sys.stderr)

    failed = [result for result in results if result.status != "passed"]
    if failed:
        print(f"FAILED: {len(failed)} chapter companion(s) did not pass", file=sys.stderr)
        return 1
    print(f"SymPy chapter pipeline passed. Report: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
