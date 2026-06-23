#!/usr/bin/env python3
"""Deterministic Lean sorry-repair smoke loop.

This is a local Seed/Delta-style baseline: scan a Lean file for one-line
`sorry` placeholders, try a small tactic cascade in temporary copies, and emit
the resulting diff.  By default it does not edit the source file.

Usage:
    python3 tools/lean4-skills/seed_sorry_repair_smoke.py \
      lean/InfoGeometry/Eval/SorryFillerTest.lean

    python3 tools/lean4-skills/seed_sorry_repair_smoke.py FILE.lean --json
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, asdict
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]

TACTICS: tuple[str, ...] = (
    "rfl",
    "simp",
    "simpa",
    "omega",
    "linarith",
    "nlinarith",
    "ring",
    "ring_nf",
    "rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]",
    "simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]",
    "aesop",
    "grind",
    "intro h; exact h",
    "exact h",
    "exact h.1",
    "exact h.2",
    "left; exact h",
    "exact Or.inl h",
    "constructor <;> assumption",
    "constructor <;> simp",
)


@dataclass
class Attempt:
    line: int
    tactic: str | None
    success: bool
    stderr_tail: str = ""


def run_lean(lines: list[str], timeout: int) -> tuple[bool, str]:
    fd, name = tempfile.mkstemp(prefix="seed_sorry_repair_", suffix=".lean", dir="/tmp")
    tmp = Path(name)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.writelines(lines)
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
        return proc.returncode == 0, proc.stdout + proc.stderr
    except subprocess.TimeoutExpired as exc:
        return False, f"timeout after {timeout}s\n{exc}"
    finally:
        tmp.unlink(missing_ok=True)


def find_sorry_lines(lines: list[str]) -> list[int]:
    pattern = re.compile(r"^\s*sorry\b")
    return [i for i, line in enumerate(lines) if pattern.search(line)]


def replace_first_sorry(line: str, tactic: str) -> str:
    return re.sub(r"\bsorry\b", tactic, line, count=1)


def repair_file(path: Path, timeout: int, max_sorries: int | None) -> tuple[list[str], list[Attempt]]:
    original = path.read_text(encoding="utf-8").splitlines(keepends=True)
    current = original[:]
    attempts: list[Attempt] = []
    sorry_lines = find_sorry_lines(current)
    if max_sorries is not None:
        sorry_lines = sorry_lines[:max_sorries]

    for idx in sorry_lines:
        if idx >= len(current) or "sorry" not in current[idx]:
            continue
        closed = False
        last_output = ""
        for tactic in TACTICS:
            candidate = current[:]
            candidate[idx] = replace_first_sorry(candidate[idx], tactic)
            ok, output = run_lean(candidate, timeout)
            last_output = output
            if ok:
                current = candidate
                attempts.append(Attempt(idx + 1, tactic, True))
                closed = True
                break
        if not closed:
            tail = "\n".join(last_output.splitlines()[-20:])
            attempts.append(Attempt(idx + 1, None, False, tail))

    return current, attempts


def unified_diff(path: Path, repaired: list[str]) -> str:
    original = path.read_text(encoding="utf-8").splitlines(keepends=True)
    return "".join(
        difflib.unified_diff(
            original,
            repaired,
            fromfile=str(path),
            tofile=f"{path} (repaired candidate)",
        )
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path)
    parser.add_argument("--timeout", type=int, default=20)
    parser.add_argument("--max-sorries", type=int, default=None)
    parser.add_argument("--apply", action="store_true", help="write successful candidate back to FILE")
    parser.add_argument("--json", action="store_true", help="emit machine-readable summary")
    args = parser.parse_args()

    path = args.file
    if not path.exists():
        print(f"missing file: {path}", file=sys.stderr)
        return 2

    repaired, attempts = repair_file(path, args.timeout, args.max_sorries)
    closed = sum(1 for a in attempts if a.success)
    failed = sum(1 for a in attempts if not a.success)
    diff = unified_diff(path, repaired)

    if args.apply and diff:
        path.write_text("".join(repaired), encoding="utf-8")

    if args.json:
        print(json.dumps({
            "file": str(path),
            "closed": closed,
            "failed": failed,
            "attempts": [asdict(a) for a in attempts],
            "applied": bool(args.apply and diff),
            "diff": diff,
        }, indent=2))
    else:
        print(f"closed={closed} failed={failed} file={path}")
        for attempt in attempts:
            status = "closed" if attempt.success else "failed"
            print(f"{status}: line {attempt.line}: {attempt.tactic}")
        if diff:
            print(diff)

    return 0 if failed == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
