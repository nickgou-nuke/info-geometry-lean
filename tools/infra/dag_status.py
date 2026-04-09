#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.artifacts import load_decl_index_meta, load_json_dict
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
else:
    from tools.infra.artifacts import load_decl_index_meta, load_json_dict
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Show the active DAG toolchain configuration and authoritative artifact state."
    )
    parser.add_argument(
        "--config",
        help="Optional dag-toolchain.json override. Defaults to dag-toolchain.local.json when present, else dag-toolchain.json.",
    )
    return parser.parse_args()


def parse_iso_timestamp(raw: Any) -> datetime | None:
    if not isinstance(raw, str) or not raw:
        return None
    try:
        return datetime.fromisoformat(raw)
    except ValueError:
        return None


def format_age(delta: timedelta) -> str:
    total_seconds = max(0, int(delta.total_seconds()))
    days, rem = divmod(total_seconds, 86400)
    hours, rem = divmod(rem, 3600)
    minutes, seconds = divmod(rem, 60)
    if days:
        return f"{days}d {hours}h"
    if hours:
        return f"{hours}h {minutes}m"
    if minutes:
        return f"{minutes}m {seconds}s"
    return f"{seconds}s"


def format_sync(delta_seconds: float, *, tolerance_seconds: int = 300) -> str:
    if abs(delta_seconds) <= tolerance_seconds:
        return "in sync"
    if delta_seconds > 0:
        return f"newer by {format_age(timedelta(seconds=delta_seconds))}"
    return f"older by {format_age(timedelta(seconds=-delta_seconds))}"


def file_mtime(path: Path) -> datetime | None:
    if not path.exists():
        return None
    return datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc)


def extract_graph_coverage(report: dict[str, Any]) -> dict[str, Any]:
    summary = report.get("summary")
    if isinstance(summary, dict):
        graph_coverage = summary.get("graph_coverage")
        if isinstance(graph_coverage, dict):
            return graph_coverage
    coverage = report.get("coverage")
    return coverage if isinstance(coverage, dict) else {}


def top_label(rows: Any) -> str:
    if not isinstance(rows, list) or not rows:
        return "-"
    first = rows[0]
    if not isinstance(first, dict):
        return "-"
    label = first.get("label", "-")
    count = first.get("count", 0)
    return f"{label} ({count})"


def main() -> int:
    args = parse_args()
    config = load_dag_toolchain_config(args.config)

    meta_path = config.authoritative_artifacts.index_dir / "meta.json"
    meta = load_decl_index_meta(meta_path) or {}
    coverage_report = (
        load_json_dict(config.derived_reports.coverage_report_json)
        if config.derived_reports.coverage_report_json.exists()
        else {}
    )
    leakage_report = (
        load_json_dict(config.policies.leakage.report_sidecar)
        if config.policies.leakage.report_sidecar.exists()
        else {}
    )

    meta_timestamp = parse_iso_timestamp(meta.get("timestamp"))
    now = datetime.now(timezone.utc)
    coverage_mtime = file_mtime(config.derived_reports.coverage_report_json)
    leakage_mtime = file_mtime(config.policies.leakage.report_sidecar)

    required_paths = [
        config.authoritative_artifacts.graph_out,
        config.authoritative_artifacts.structure_out,
        meta_path,
    ]
    missing_paths = [repo_display_path(path) for path in required_paths if not path.exists()]
    freshness = "complete" if not missing_paths else f"missing {', '.join(missing_paths)}"

    print("DAG status")
    print(f"config: {repo_display_path(config.config_path)}")
    print(f"config schemaVersion: {config.schema_version}")
    print(f"buildTarget: {config.build.build_target}")
    print(f"importRoot: {config.build.import_root}")
    print(f"namespaceFilter: {config.build.namespace_filter}")
    print(f"runMode: {config.build.run_mode}")
    print()
    print("Artifacts")
    print(f"authoritative set: {freshness}")
    print(f"artifact schemaVersion: {meta.get('schemaVersion', '-')}")
    print(f"timestamp: {meta.get('timestamp', '-')}")
    print(f"oleanHash: {meta.get('oleanHash', '-')}")
    print(
        "counts: "
        f"nodes={meta.get('nodeCount', '-')}, "
        f"edges={meta.get('edgeCount', '-')}, "
        f"morphisms={meta.get('morphismCount', '-')}"
    )
    if meta_timestamp is not None:
        print(f"artifact age: {format_age(now - meta_timestamp)}")
    else:
        print("artifact age: unknown")
    if meta_timestamp is not None and coverage_mtime is not None:
        print(f"coverage report: {format_sync((coverage_mtime - meta_timestamp).total_seconds())}")
    else:
        print("coverage report: missing")
    if meta_timestamp is not None and leakage_mtime is not None:
        print(f"leakage sidecar: {format_sync((leakage_mtime - meta_timestamp).total_seconds(), tolerance_seconds=30)}")
    else:
        print("leakage sidecar: missing")
    print()
    print("Coverage")
    graph_coverage = extract_graph_coverage(coverage_report)
    print(f"repo_decl_files: {graph_coverage.get('repo_decl_files', '-')}")
    print(f"decl_index_files: {graph_coverage.get('decl_index_files', '-')}")
    print(f"missing_decl_files: {graph_coverage.get('missing_decl_files_count', '-')}")
    print(f"is_partial: {graph_coverage.get('is_partial', '-')}")
    print()
    print("Leakage")
    print(f"droppedEdges: {leakage_report.get('droppedEdges', '-')}")
    print(
        "breakdown: "
        f"external={leakage_report.get('dstOutsideModuleEdges', '-')}, "
        f"internalGenerated={leakage_report.get('dstInsideModuleGeneratedEdges', '-')}, "
        f"internalStable={leakage_report.get('dstInsideModuleStableEdges', '-')}, "
        f"unknown={leakage_report.get('dstUnknownEdges', '-')}"
    )
    print(f"top external module: {top_label(leakage_report.get('topExternalModules'))}")
    print(f"top internal module: {top_label(leakage_report.get('topInternalModules'))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
