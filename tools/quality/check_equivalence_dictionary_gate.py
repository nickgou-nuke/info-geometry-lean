#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


ROOT = repo_root()
DEFAULT_REPORT = ROOT / "reports" / "dag" / "equivalence-dictionary.json"
DEFAULT_POLICY = ROOT / "tools" / "quality" / "equivalence_dictionary_gate.json"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Gate unresolved-token growth in the maintained equivalence dictionary "
            "against policy baselines."
        )
    )
    parser.add_argument(
        "--report",
        default=str(DEFAULT_REPORT.relative_to(ROOT)),
        help="Path to equivalence dictionary JSON report.",
    )
    parser.add_argument(
        "--policy",
        default=str(DEFAULT_POLICY.relative_to(ROOT)),
        help="Path to unresolved-growth policy JSON.",
    )
    return parser.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as ex:
        raise SystemExit(f"[equivalence-gate] failed reading {path}: {ex}") from ex
    if not isinstance(payload, dict):
        raise SystemExit(f"[equivalence-gate] expected object JSON at {path}")
    return payload


def compute_report_metrics(report: dict[str, Any]) -> dict[str, int]:
    summary = report.get("summary", {})
    if not isinstance(summary, dict):
        summary = {}

    unresolved_rows = report.get("unresolvedHeads", [])
    if not isinstance(unresolved_rows, list):
        unresolved_rows = []

    unresolved_total = sum(int(row.get("count", 0)) for row in unresolved_rows if isinstance(row, dict))
    unresolved_unique = len([row for row in unresolved_rows if isinstance(row, dict)])

    metrics: dict[str, int] = {}
    metrics["unresolved_head_token_total"] = int(summary.get("unresolved_head_token_total", unresolved_total))
    metrics["unresolved_head_unique_count"] = int(summary.get("unresolved_head_unique_count", unresolved_unique))
    # Ambiguous short heads are expected in a large Lean development (`star`,
    # `trace`, overloaded algebraic operations).  The growth gate tracks the
    # narrower missing-nonlocal surface instead of treating overloads as debt.
    metrics["unresolved_missing_nonlocal_token_total"] = int(
        summary.get("unresolved_missing_nonlocal_token_total", 0)
    )
    metrics["unresolved_missing_nonlocal_unique_count"] = int(
        summary.get("unresolved_missing_nonlocal_unique_count", 0)
    )
    return metrics


def main() -> int:
    args = parse_args()
    report_path = normalize_user_path(args.report, DEFAULT_REPORT)
    policy_path = normalize_user_path(args.policy, DEFAULT_POLICY)

    if not report_path.exists():
        print(f"[equivalence-gate] missing report: {report_path}")
        return 1
    if not policy_path.exists():
        print(f"[equivalence-gate] missing policy: {policy_path}")
        return 1

    report = load_json(report_path)
    policy = load_json(policy_path)

    rows = policy.get("thresholds", [])
    if not isinstance(rows, list) or not rows:
        print(f"[equivalence-gate] policy has no `thresholds` rows: {policy_path}")
        return 1

    metrics = compute_report_metrics(report)
    failures: list[str] = []

    print("[equivalence-gate] checking unresolved-growth thresholds")
    for row in rows:
        if not isinstance(row, dict):
            failures.append("invalid threshold row: expected object")
            continue
        metric = str(row.get("metric", "")).strip()
        if not metric:
            failures.append("invalid threshold row: missing metric")
            continue
        if metric not in metrics:
            failures.append(f"metric not found in report: {metric}")
            continue
        baseline = int(row.get("baseline", 0))
        max_growth = int(row.get("maxGrowth", 0))
        current = int(metrics[metric])
        allowed = baseline + max_growth
        growth = current - baseline
        print(
            f"  - {metric}: current={current} baseline={baseline} "
            f"growth={growth} allowedMax={allowed}"
        )
        if current > allowed:
            failures.append(
                f"{metric} exceeded: current={current} > baseline+maxGrowth={allowed} "
                f"(baseline={baseline}, maxGrowth={max_growth})"
            )

    if failures:
        print("[equivalence-gate] FAILED")
        for msg in failures:
            print(f"  - {msg}")
        return 1

    print("[equivalence-gate] PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
