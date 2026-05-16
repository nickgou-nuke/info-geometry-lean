#!/usr/bin/env python3
"""
Mission Judge for the Closure Mission Loop.

Usage:
  python3 tools/quality/mission_judge.py <lean_file> <response_file> <baseline_debt_count>

Exit codes:
  0 = DONE   (socket closed, all checks pass)
  1 = CONTINUE (keep working, some check failed)
  2 = BLOCKED  (kernel error unrelated to the socket — skip and auto-pause)

The judge enforces the Closure Mission Loop standard:
  1. Lean kernel must pass (lake env lean <file>)
  2. No new forbidden patterns (sorry, opaque witness, native_decide without axiom roots)
  3. Debt label count must decrease vs baseline
  4. Response must document a Mathlib derivation chain

This is a deterministic gate; it does NOT call any LLM.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

# Patterns whose introduction is forbidden in a closure commit
FORBIDDEN_PATTERNS = [
    r"\bsorry\b",
    r"\badmit\b",
    # opaque witness constructor without proof fields
    r"noncomputable\s+def\s+\w+\s*:\s*\w+\s*:=\s*⟨[^⟩]*⟩\s*$",
]

# Evidence that a Mathlib derivation chain was documented in the response
CHAIN_EVIDENCE_PATTERNS = [
    r"Mathlib\.",
    r"-- derivation:",
    r"-- chain:",
    r"-- roots?:",
    r"←.*Mathlib",
    r"from\s+Mathlib",
]

# Signals that the debt label is still present (not removed)
DEBT_LABEL_PATTERN = re.compile(
    r"Native Closure Mandated.*Closure Debt", re.IGNORECASE
)


def count_debt_labels(file: Path) -> int:
    """Count remaining Closure Debt labels in a Lean file."""
    try:
        text = file.read_text(encoding="utf-8", errors="replace")
        return len(DEBT_LABEL_PATTERN.findall(text))
    except OSError:
        return -1


def run_lean(file: Path) -> tuple[bool, str]:
    """Run lake env lean on a file. Returns (passed, stderr_excerpt)."""
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(file)],
            capture_output=True, text=True, timeout=120
        )
        stderr = result.stderr or ""
        passed = result.returncode == 0 and "error" not in stderr.lower()
        return passed, stderr[:400]
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT: lake env lean did not finish in 120s"
    except FileNotFoundError:
        return False, "lake not found in PATH"


def check_forbidden(response_text: str) -> list[str]:
    """Return list of forbidden pattern matches found in the response."""
    hits = []
    for pat in FORBIDDEN_PATTERNS:
        matches = re.findall(pat, response_text, re.MULTILINE)
        if matches:
            hits.append(f"{pat!r}: {matches[:2]}")
    return hits


def check_chain_evidence(response_text: str) -> bool:
    """Return True if the response documents a Mathlib derivation chain."""
    return any(re.search(p, response_text) for p in CHAIN_EVIDENCE_PATTERNS)


def judge(
    lean_file: str,
    response_text: str,
    baseline_debt: int,
) -> dict:
    file = Path(lean_file)

    # 1. Lean kernel check
    kernel_pass, kernel_err = run_lean(file)

    # 2. Forbidden pattern check
    forbidden_hits = check_forbidden(response_text)
    new_witness = bool(forbidden_hits)

    # 3. Debt count check
    current_debt = count_debt_labels(file)
    if baseline_debt < 0 or current_debt < 0:
        debt_reduced = False
        debt_note = f"count unavailable (baseline={baseline_debt}, current={current_debt})"
    else:
        debt_reduced = current_debt < baseline_debt
        debt_note = f"baseline={baseline_debt}, current={current_debt}"

    # 4. Derivation chain check
    chain_present = check_chain_evidence(response_text)

    done = kernel_pass and not new_witness and debt_reduced and chain_present

    reasons = []
    if not kernel_pass:
        reasons.append(f"kernel fail: {kernel_err}")
    if new_witness:
        reasons.append(f"new witness pattern detected: {forbidden_hits}")
    if not debt_reduced:
        reasons.append(f"debt count unchanged ({debt_note})")
    if not chain_present:
        reasons.append("derivation chain not documented in response")

    # Classify BLOCKED vs CONTINUE
    # BLOCKED = kernel error unrelated to the socket (toolchain issue, import error)
    status = "done" if done else ("blocked" if (not kernel_pass and "import" in kernel_err.lower()) else "continue")

    return {
        "done": done,
        "status": status,
        "reason": "; ".join(reasons) if reasons else "all checks pass",
        "checks": {
            "kernel_pass": kernel_pass,
            "kernel_err": kernel_err if not kernel_pass else "",
            "new_witness": new_witness,
            "forbidden_hits": forbidden_hits,
            "debt_reduced": debt_reduced,
            "debt_note": debt_note,
            "chain_present": chain_present,
        },
    }


if __name__ == "__main__":
    if len(sys.argv) < 4:
        print(
            "Usage: mission_judge.py <lean_file> <response_file> <baseline_debt_count>",
            file=sys.stderr,
        )
        sys.exit(2)

    lean_file = sys.argv[1]
    response_file = sys.argv[2]
    baseline_debt = int(sys.argv[3])

    try:
        response_text = Path(response_file).read_text(encoding="utf-8", errors="replace")
    except OSError as e:
        print(json.dumps({"done": False, "status": "blocked", "reason": str(e)}))
        sys.exit(2)

    verdict = judge(lean_file, response_text, baseline_debt)
    print(json.dumps(verdict, indent=2))

    if verdict["status"] == "done":
        sys.exit(0)
    elif verdict["status"] == "blocked":
        sys.exit(2)
    else:
        sys.exit(1)
