#!/usr/bin/env python3
"""Regression gate for Socratic oracle prompt GEPA reports."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


FORBIDDEN = (
    re.compile(r"\b(?:use|add|insert|leave|keep)\s+`?(?:sorry|admit|axiom)`?", re.IGNORECASE),
    re.compile(r"\b(?:sorry|admit|axiom)s?\s+(?:are|is)\s+(?:ok|okay|acceptable|allowed)\b", re.IGNORECASE),
    re.compile(r"\b(?:show|reveal|provide|recover)\s+(?:hidden\s+)?chain[- ]of[- ]thought\b", re.IGNORECASE),
    re.compile(r"\bignore (?:the )?compiler\b", re.IGNORECASE),
)


def load(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def forbidden_match(text: str, pattern: re.Pattern[str]) -> bool:
    for match in pattern.finditer(text):
        prefix = text[max(0, match.start() - 16):match.start()].lower()
        if "do not " in prefix or "never " in prefix:
            continue
        return True
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--min-trials", type=int, default=3)
    parser.add_argument("--allow-keep-builtin", action="store_true")
    args = parser.parse_args()

    report = load(args.report)
    recommendation = str(report.get("recommendation", ""))
    best = report.get("best") if isinstance(report.get("best"), dict) else {}
    baseline = report.get("baseline") if isinstance(report.get("baseline"), dict) else {}
    failures: list[str] = []

    if recommendation == "keep_builtin":
        if args.allow_keep_builtin:
            print("oracle_prompt_regression_gate: ok (keep_builtin)")
            return 0
        failures.append("report recommends keep_builtin; no deployable prompt improvement")

    best_trials = int(best.get("empirical_trials") or 0)
    if best_trials < args.min_trials:
        failures.append(f"best candidate has insufficient empirical trials: {best_trials} < {args.min_trials}")

    if int(best.get("forbidden_hits") or 0) > 0:
        failures.append("best candidate contains forbidden prompt patterns")

    if baseline:
        best_fitness = float(best.get("fitness") or 0.0)
        baseline_fitness = float(baseline.get("fitness") or 0.0)
        if best_fitness < baseline_fitness:
            failures.append(f"best fitness regressed below baseline: {best_fitness:.4f} < {baseline_fitness:.4f}")

    text_path = best.get("text_path")
    if text_path:
        path = Path(text_path)
        if not path.is_absolute():
            path = Path.cwd() / path
        if path.exists():
            text = path.read_text(encoding="utf-8")
            for pattern in FORBIDDEN:
                if forbidden_match(text, pattern):
                    failures.append(f"best text matches forbidden regex: {pattern.pattern}")

    if failures:
        print("oracle_prompt_regression_gate: FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print("oracle_prompt_regression_gate: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
