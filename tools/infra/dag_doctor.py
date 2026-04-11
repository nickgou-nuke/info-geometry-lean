#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import shutil
import sys
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.build_lock import DEFAULT_BUILD_LOCK_PATH, read_lock_metadata
    from tools.infra.artifacts import EXPECTED_INDEXER_SCHEMA_VERSION, load_decl_index_meta, load_json_dict
    from tools.infra.build import compute_olean_content_hash
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.infra.timings import (
        load_indexer_timing,
        load_report_timing,
        report_timing_json_path,
        timing_matches_meta,
        top_timing_rows,
    )
    from tools.pathing import repo_root
else:
    from tools.build_lock import DEFAULT_BUILD_LOCK_PATH, read_lock_metadata
    from tools.infra.artifacts import EXPECTED_INDEXER_SCHEMA_VERSION, load_decl_index_meta, load_json_dict
    from tools.infra.build import compute_olean_content_hash
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.infra.timings import (
        load_indexer_timing,
        load_report_timing,
        report_timing_json_path,
        timing_matches_meta,
        top_timing_rows,
    )
    from tools.pathing import repo_root


@dataclass(frozen=True)
class CheckResult:
    level: str
    label: str
    detail: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Inspect the managed DAG lane for config, build, artifact, report, and environment issues."
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


def add(results: list[CheckResult], level: str, label: str, detail: str) -> None:
    results.append(CheckResult(level=level, label=label, detail=detail))


def has_result(results: list[CheckResult], label: str, *, levels: set[str] | None = None) -> bool:
    for result in results:
        if result.label != label:
            continue
        if levels is None or result.level in levels:
            return True
    return False


def suggestion_lines(results: list[CheckResult]) -> list[str]:
    lines: list[str] = []
    if has_result(results, "authoritative artifacts", levels={"fail"}) or has_result(
        results, "meta", levels={"fail"}
    ) or has_result(results, "meta schema", levels={"fail"}) or has_result(
        results, "meta importRoot", levels={"fail"}
    ) or has_result(results, "meta namespace", levels={"fail"}) or has_result(
        results, "olean hash", levels={"warn"}
    ):
        lines.append("lake script run dagRefresh")
    if has_result(results, "coverage report", levels={"warn", "fail"}) or has_result(
        results, "coverage policy", levels={"warn", "fail"}
    ) or has_result(results, "coverage freshness", levels={"warn", "fail"}) or has_result(
        results, "leakage sidecar", levels={"warn", "fail"}
    ) or has_result(results, "report timing", levels={"warn", "fail"}):
        lines.append("lake script run dagReports")
    if has_result(results, "build lock", levels={"warn"}):
        lines.append("lake script run dagStatus")
    if any(result.level in {"warn", "fail"} for result in results):
        lines.append("lake script run dagAll")
    if has_result(results, "lake", levels={"fail"}) or has_result(results, "python3", levels={"fail"}) or has_result(
        results, "tmp", levels={"fail"}
    ):
        lines.append("Fix the local environment first; rerun: lake script run dagDoctor")

    seen: set[str] = set()
    unique: list[str] = []
    for line in lines:
        if line in seen:
            continue
        seen.add(line)
        unique.append(line)
    return unique


def process_exists(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def writable_directory(path: Path) -> bool:
    return path.exists() and path.is_dir() and os.access(path, os.W_OK)


def preferred_matplotlib_dir() -> Path:
    return repo_root() / ".artifacts" / "matplotlib"


def main() -> int:
    args = parse_args()
    root = repo_root()
    results: list[CheckResult] = []

    try:
        config = load_dag_toolchain_config(args.config)
    except Exception as exc:
        print("DAG doctor")
        print(f"[FAIL] config: {exc}")
        return 1

    add(results, "ok", "config", f"loaded {repo_display_path(config.config_path, root)}")
    add(
        results,
        "ok",
        "build config",
        (
            f"buildTarget={config.build.build_target}, importRoot={config.build.import_root}, "
            f"namespaceFilter={config.build.namespace_filter}, runMode={config.build.run_mode}"
        ),
    )

    lake_path = shutil.which("lake")
    if lake_path:
        add(results, "ok", "lake", lake_path)
    else:
        add(results, "fail", "lake", "not found on PATH")

    python_path = shutil.which("python3") or sys.executable
    if python_path:
        add(results, "ok", "python3", python_path)
    else:
        add(results, "fail", "python3", "not found on PATH")

    if config.build.run_mode == "exe":
        built_exe = root / ".lake" / "build" / "bin" / "dagIndexer"
        if built_exe.exists():
            add(results, "ok", "dagIndexer exe", repo_display_path(built_exe, root))
        else:
            add(results, "warn", "dagIndexer exe", "not built yet; dagRefresh will prebuild it")

    meta_path = config.authoritative_artifacts.index_dir / "meta.json"
    authoritative_paths = [
        config.authoritative_artifacts.graph_out,
        config.authoritative_artifacts.structure_out,
        meta_path,
    ]
    missing_authoritative = [repo_display_path(path, root) for path in authoritative_paths if not path.exists()]
    if missing_authoritative:
        add(results, "fail", "authoritative artifacts", f"missing {', '.join(missing_authoritative)}")
    else:
        add(results, "ok", "authoritative artifacts", "complete")

    meta = load_decl_index_meta(meta_path) or {}
    meta_timestamp = parse_iso_timestamp(meta.get("timestamp")) if meta else None
    if not meta:
        add(results, "fail", "meta", f"missing or unreadable {repo_display_path(meta_path, root)}")
    else:
        schema_version = meta.get("schemaVersion")
        if schema_version == EXPECTED_INDEXER_SCHEMA_VERSION:
            add(results, "ok", "meta schema", f"schemaVersion={schema_version}")
        else:
            add(
                results,
                "fail",
                "meta schema",
                f"expected schemaVersion={EXPECTED_INDEXER_SCHEMA_VERSION}, got {schema_version}",
            )

        if meta.get("importRoot") == config.build.import_root:
            add(results, "ok", "meta importRoot", config.build.import_root)
        else:
            add(
                results,
                "fail",
                "meta importRoot",
                f"meta={meta.get('importRoot', '-')}, config={config.build.import_root}",
            )

        if meta.get("nsFilter") == config.build.namespace_filter:
            add(results, "ok", "meta namespace", config.build.namespace_filter)
        else:
            add(
                results,
                "fail",
                "meta namespace",
                f"meta={meta.get('nsFilter', '-')}, config={config.build.namespace_filter}",
            )

        if meta_timestamp is not None:
            add(results, "ok", "artifact timestamp", f"{meta_timestamp.isoformat()} ({format_age(datetime.now(timezone.utc) - meta_timestamp)} old)")
        else:
            add(results, "warn", "artifact timestamp", "missing or invalid ISO timestamp")

        current_hash = compute_olean_content_hash(root)
        stored_hash = meta.get("oleanHash")
        if current_hash and stored_hash == current_hash:
            add(results, "ok", "olean hash", "artifacts match current build products")
        elif current_hash and stored_hash:
            add(results, "warn", "olean hash", "artifacts appear stale relative to current build products")
        else:
            add(results, "warn", "olean hash", "missing current or stored olean hash")

    indexer_timing = load_indexer_timing(config.authoritative_artifacts.index_dir)
    if not indexer_timing:
        add(results, "warn", "indexer timing", "missing structured or parsable indexer timing")
    else:
        total_ms = indexer_timing.get("total_ms")
        slow_rows = top_timing_rows(indexer_timing, limit=1)
        slow_label = slow_rows[0]["label"] if slow_rows else "-"
        slow_ms = slow_rows[0]["elapsed_ms"] if slow_rows else None
        match_indexer = timing_matches_meta(indexer_timing, meta)
        if match_indexer is False:
            add(results, "warn", "indexer timing", "timing sidecar is stale relative to authoritative artifacts")
        else:
            add(
                results,
                "ok",
                "indexer timing",
                f"total={total_ms}ms, slowest={slow_label} ({slow_ms}ms)",
            )

    coverage_path = config.derived_reports.coverage_report_json
    if not coverage_path.exists():
        add(results, "warn", "coverage report", f"missing {repo_display_path(coverage_path, root)}")
        coverage_report = {}
    else:
        try:
            coverage_report = load_json_dict(coverage_path)
        except Exception as exc:
            add(results, "fail", "coverage report", f"unreadable {repo_display_path(coverage_path, root)} ({exc})")
            coverage_report = {}
        coverage = extract_graph_coverage(coverage_report)
        missing_decl_files = int(coverage.get("missing_decl_files_count", 0))
        is_partial = bool(coverage.get("is_partial", True))
        if config.policies.coverage.require_full_coverage and is_partial:
            add(results, "fail", "coverage policy", "coverage report is partial")
        elif missing_decl_files > config.policies.coverage.max_missing_decl_files:
            add(
                results,
                "fail",
                "coverage policy",
                f"missing_decl_files_count={missing_decl_files} exceeds {config.policies.coverage.max_missing_decl_files}",
            )
        else:
            add(
                results,
                "ok",
                "coverage policy",
                (
                    f"repo_decl_files={coverage.get('repo_decl_files', '-')}, "
                    f"decl_index_files={coverage.get('decl_index_files', '-')}, "
                    f"missing_decl_files_count={missing_decl_files}"
                ),
            )

        meta_timestamp = parse_iso_timestamp(meta.get("timestamp"))
        coverage_mtime = file_mtime(coverage_path)
        if meta_timestamp is not None and coverage_mtime is not None:
            delta = coverage_mtime - meta_timestamp
            if delta.total_seconds() < -300:
                add(results, "warn", "coverage freshness", f"older than authoritative artifacts by {format_age(-delta)}")
            else:
                add(results, "ok", "coverage freshness", "coverage report is not stale")
        else:
            add(results, "warn", "coverage freshness", "unable to compare coverage report against authoritative artifacts")

    leakage_path = config.policies.leakage.report_sidecar
    if not leakage_path.exists():
        add(results, "warn", "leakage sidecar", f"missing {repo_display_path(leakage_path, root)}")
    else:
        try:
            leakage_report = load_json_dict(leakage_path)
        except Exception as exc:
            add(results, "warn", "leakage sidecar", f"unreadable {repo_display_path(leakage_path, root)} ({exc})")
            leakage_report = {}
        required_leakage_keys = {
            "droppedEdges",
            "dstOutsideModuleEdges",
            "dstInsideModuleGeneratedEdges",
            "dstInsideModuleStableEdges",
            "dstUnknownEdges",
        }
        if required_leakage_keys.issubset(leakage_report.keys()):
            add(
                results,
                "ok",
                "leakage sidecar",
                (
                    f"droppedEdges={leakage_report.get('droppedEdges')}, "
                    f"internalStable={leakage_report.get('dstInsideModuleStableEdges')}"
                ),
            )
        else:
            add(results, "warn", "leakage sidecar", "present but missing expected breakdown fields")

    report_timing = load_report_timing(report_timing_json_path(root))
    if not report_timing:
        add(results, "warn", "report timing", "missing report-timing.json")
    else:
        total_ms = report_timing.get("total_ms")
        slow_rows = top_timing_rows(report_timing, limit=1)
        slow_label = slow_rows[0]["label"] if slow_rows else "-"
        slow_ms = slow_rows[0]["elapsed_ms"] if slow_rows else None
        match_report = timing_matches_meta(report_timing, meta)
        if match_report is False:
            add(results, "warn", "report timing", "report timing is stale relative to authoritative artifacts")
        else:
            add(
                results,
                "ok",
                "report timing",
                f"total={total_ms}ms, slowest={slow_label} ({slow_ms}ms)",
            )

    lock_meta = read_lock_metadata(DEFAULT_BUILD_LOCK_PATH)
    if not lock_meta:
        add(results, "ok", "build lock", "not held")
    else:
        pid = lock_meta.get("pid")
        owner = lock_meta.get("owner", "unknown")
        if isinstance(pid, int) and process_exists(pid):
            add(results, "warn", "build lock", f"held by owner={owner}, pid={pid}")
        else:
            add(results, "warn", "build lock", f"stale metadata present for owner={owner}, pid={pid}")

    tmp_dir = Path("/tmp")
    if writable_directory(tmp_dir):
        add(results, "ok", "tmp", "/tmp is writable")
    else:
        add(results, "fail", "tmp", "/tmp is not writable")

    mpl_env = os.environ.get("MPLCONFIGDIR")
    if mpl_env:
        mpl_path = Path(mpl_env)
        if writable_directory(mpl_path):
            add(results, "ok", "matplotlib cache", f"MPLCONFIGDIR={mpl_env}")
        else:
            add(results, "warn", "matplotlib cache", f"MPLCONFIGDIR is set but not writable: {mpl_env}")
    else:
        default_mpl_dir = Path.home() / ".config" / "matplotlib"
        preferred_dir = preferred_matplotlib_dir()
        if writable_directory(preferred_dir):
            add(results, "ok", "matplotlib cache", f"managed report cache available: {repo_display_path(preferred_dir, root)}")
        elif writable_directory(default_mpl_dir):
            add(results, "ok", "matplotlib cache", f"default cache dir writable: {default_mpl_dir}")
        else:
            add(
                results,
                "warn",
                "matplotlib cache",
                (
                    f"default cache dir not writable: {default_mpl_dir}; "
                    f"prefer MPLCONFIGDIR={repo_display_path(preferred_matplotlib_dir(), root)}"
                ),
            )

    print("DAG doctor")
    for result in results:
        print(f"[{result.level.upper()}] {result.label}: {result.detail}")

    fail_count = sum(1 for result in results if result.level == "fail")
    warn_count = sum(1 for result in results if result.level == "warn")
    ok_count = sum(1 for result in results if result.level == "ok")
    print()
    print(f"Summary: ok={ok_count} warn={warn_count} fail={fail_count}")
    next_steps = suggestion_lines(results)
    if next_steps:
        print()
        print("Next commands:")
        for i, step in enumerate(next_steps, start=1):
            print(f"{i}. {step}")
    return 1 if fail_count else 0


if __name__ == "__main__":
    raise SystemExit(main())
