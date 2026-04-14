#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def run_step(step_name: str, cmd: list[str]) -> None:
    print(f"[full-dag] {step_name}: {' '.join(cmd)}")
    subprocess.run(cmd, cwd=ROOT, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run the repo-native DAG/policy toolchain in strict order to avoid stale-artifact contamination."
        )
    )
    parser.add_argument(
        "--skip-audit",
        action="store_true",
        help="Skip InfoGeometry.Audit and InfoGeometry.AuditStrict preflight.",
    )
    parser.add_argument(
        "--write-policy-baseline",
        action="store_true",
        help="Refresh canonical policy baseline before final policy validation.",
    )
    args = parser.parse_args()

    if not args.skip_audit:
        run_step(
            "audit",
            ["python3", "tools/infra/run_locked_lake_build.py", "InfoGeometry.Audit"],
        )
        run_step(
            "audit-strict",
            ["python3", "tools/infra/run_locked_lake_build.py", "InfoGeometry.AuditStrict"],
        )

    run_step("refresh-decl-graph", ["python3", "tools/infra/refresh_decl_graph.py"])
    run_step(
        "source-sink-compression",
        ["python3", "tools/infra/generate_source_sink_compression.py"],
    )
    run_step(
        "process-flow-report",
        [
            "python3",
            "tools/infra/generate_process_flow_report.py",
            "--input-dir",
            "artifacts/dag/process-flow",
            "--report-out",
            "reports/dag/process-flow-report.md",
            "--json-out",
            "reports/dag/process-flow-report.json",
        ],
    )
    run_step(
        "semantic-flow-report",
        [
            "python3",
            "tools/infra/generate_semantic_flow_report.py",
            "--input-dir",
            "artifacts/dag/process-flow",
            "--json-out",
            "reports/dag/semantic-flow-report.json",
            "--md-out",
            "reports/dag/semantic-flow-report.md",
        ],
    )
    run_step(
        "semantic-flow-check",
        [
            "python3",
            "tools/infra/check_semantic_flow_report.py",
            "--input-dir",
            "artifacts/dag/process-flow",
            "--json-out",
            "reports/dag/semantic-flow-report.json",
            "--md-out",
            "reports/dag/semantic-flow-report.md",
            "--skip-generate",
        ],
    )
    run_step(
        "causal-report",
        [
            "python3",
            "tools/infra/generate_causal_report.py",
            "--out",
            "reports/dag/true-root-order.md",
            "--json-out",
            "reports/dag/true-root-order.json",
        ],
    )

    if args.write_policy_baseline:
        run_step(
            "policy-baseline",
            ["python3", "tools/infra/canonical_policy_lint.py", "--write-baseline"],
        )

    run_step("policy-lint", ["python3", "tools/infra/canonical_policy_lint.py"])
    print("[full-dag] completed successfully")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
