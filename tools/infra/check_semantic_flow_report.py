#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root

DEFAULT_INPUT_DIR = "artifacts/dag/process-flow"
DEFAULT_JSON_OUT = "reports/dag/semantic-flow-report.json"
DEFAULT_MD_OUT = "reports/dag/semantic-flow-report.md"
EXPECTED_REPORT_SCHEMA_VERSION = 1
EXPECTED_INPUT_SCHEMA_VERSION = 4

REQUIRED_TOP_LEVEL_KEYS = {
    "summary",
    "polarityHistogram",
    "defectTagHistogram",
    "topChiralSources",
    "topChiralSinks",
    "topObstructionNodes",
    "topObstructionEdges",
    "topEntropyPairs",
    "topLoopObstructions",
    "topWilsonFrustration",
}

REQUIRED_SUMMARY_KEYS = {
    "schemaVersion",
    "inputSchemaVersion",
    "nodeCount",
    "edgeCount",
    "sccCount",
    "nontrivialSccCount",
    "iterations",
    "alpha",
    "maxDelta",
    "totalEntropyProduction",
    "totalHarmonicMass",
    "totalFrustratedEdges",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run and validate the semantic flow report. "
            "Checks output files and required JSON schema keys."
        )
    )
    parser.add_argument("--input-dir", default=DEFAULT_INPUT_DIR, help="Process-flow artifact directory.")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="Semantic-flow JSON output path.")
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT, help="Semantic-flow Markdown output path.")
    parser.add_argument(
        "--allow-missing-input",
        action="store_true",
        help="If artifacts are missing, exit 0 instead of failing.",
    )
    parser.add_argument(
        "--skip-generate",
        action="store_true",
        help="Validate existing outputs without running generate_semantic_flow_report.py.",
    )
    return parser.parse_args()


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(msg)


def run_generate(root: Path, input_dir: Path, json_out: Path, md_out: Path, allow_missing: bool = False) -> None:
    cmd = [
        sys.executable,
        "tools/infra/generate_semantic_flow_report.py",
        "--input-dir",
        str(input_dir),
        "--json-out",
        str(json_out),
        "--md-out",
        str(md_out),
    ]
    if allow_missing:
        cmd.append("--allow-missing-input")
    print(f"[semantic-flow-check] running: {' '.join(cmd)}", flush=True)
    proc = subprocess.run(cmd, cwd=root, check=False)
    require(proc.returncode == 0, f"semantic-flow generator failed with exit code {proc.returncode}")


def main() -> int:
    args = parse_args()
    root = repo_root()

    input_dir = normalize_user_path(args.input_dir, root / DEFAULT_INPUT_DIR)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    if not input_dir.exists():
        if args.allow_missing_input:
            print(f"[check_semantic_flow_report] missing input directory {input_dir}, skipping.", flush=True)
            return 0
        raise SystemExit(f"missing semantic-flow input directory: {input_dir}")

    if not args.skip_generate:
        run_generate(root, input_dir, json_out, md_out, allow_missing=args.allow_missing_input)

    require(json_out.exists(), f"missing semantic-flow JSON output: {json_out}")
    require(md_out.exists(), f"missing semantic-flow Markdown output: {md_out}")
    require(json_out.stat().st_size > 0, f"semantic-flow JSON output is empty: {json_out}")
    require(md_out.stat().st_size > 0, f"semantic-flow Markdown output is empty: {md_out}")

    payload = json.loads(json_out.read_text(encoding="utf-8"))
    require(isinstance(payload, dict), "semantic-flow JSON root must be an object")

    if payload.get("status") == "skipped":
        if args.allow_missing_input:
            print(f"[check_semantic_flow_report] report was skipped: {payload.get('reason')}", flush=True)
            return 0
        raise SystemExit(f"semantic-flow report was skipped but --allow-missing-input was not provided")

    top_keys = set(payload.keys())
    missing_top = sorted(REQUIRED_TOP_LEVEL_KEYS - top_keys)
    require(not missing_top, f"semantic-flow JSON missing top-level keys: {missing_top}")

    summary = payload.get("summary")
    require(isinstance(summary, dict), "semantic-flow JSON 'summary' must be an object")

    summary_keys = set(summary.keys())
    missing_summary = sorted(REQUIRED_SUMMARY_KEYS - summary_keys)
    require(not missing_summary, f"semantic-flow summary missing keys: {missing_summary}")

    require(
        int(summary["schemaVersion"]) == EXPECTED_REPORT_SCHEMA_VERSION,
        (
            f"semantic-flow schemaVersion={summary['schemaVersion']} "
            f"!= expected {EXPECTED_REPORT_SCHEMA_VERSION}"
        ),
    )
    require(
        int(summary["inputSchemaVersion"]) == EXPECTED_INPUT_SCHEMA_VERSION,
        (
            f"semantic-flow inputSchemaVersion={summary['inputSchemaVersion']} "
            f"!= expected {EXPECTED_INPUT_SCHEMA_VERSION}"
        ),
    )

    for numeric_key in (
        "nodeCount",
        "edgeCount",
        "sccCount",
        "nontrivialSccCount",
        "iterations",
        "totalFrustratedEdges",
    ):
        require(isinstance(summary[numeric_key], int), f"summary[{numeric_key}] must be int")

    for real_key in ("alpha", "maxDelta", "totalEntropyProduction", "totalHarmonicMass"):
        require(
            isinstance(summary[real_key], (int, float)),
            f"summary[{real_key}] must be numeric",
        )

    md_head = md_out.read_text(encoding="utf-8")[:2000]
    require("# Semantic Flow Report" in md_head, "semantic-flow markdown missing report header")

    print(
        "[semantic-flow-check] OK "
        f"nodes={summary['nodeCount']} edges={summary['edgeCount']} "
        f"entropy={float(summary['totalEntropyProduction']):.6g} "
        f"frustrated={summary['totalFrustratedEdges']}",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
