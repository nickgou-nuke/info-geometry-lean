#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.artifacts import load_decl_index_meta, load_json_dict
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.pathing import repo_root
else:
    from tools.infra.artifacts import load_decl_index_meta, load_json_dict
    from tools.infra.dag_config import load_dag_toolchain_config, repo_display_path
    from tools.pathing import repo_root


MANIFEST_SCHEMA_VERSION = 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Refresh the authoritative DAG lane and write a single manifest stamp for Lake facet tracking."
    )
    parser.add_argument(
        "--config",
        help="Optional dag-toolchain.json override. Defaults to dag-toolchain.local.json when present, else dag-toolchain.json.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Forward `--force` to dag_refresh.py before writing the manifest.",
    )
    parser.add_argument(
        "--skip-prebuild",
        action="store_true",
        help="Forward `--skip-prebuild` to dag_refresh.py before writing the manifest.",
    )
    parser.add_argument(
        "--run-mode",
        choices=["exe", "run"],
        help="Override the configured indexer run mode for this invocation.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the resolved manifest refresh command without executing it.",
    )
    return parser.parse_args()


def _file_info(path: Path, root: Path) -> dict[str, Any]:
    info: dict[str, Any] = {
        "path": repo_display_path(path, root),
        "exists": path.exists(),
    }
    if not path.exists():
        return info
    stat = path.stat()
    info["mtime"] = datetime.fromtimestamp(stat.st_mtime, tz=timezone.utc).isoformat()
    info["sizeBytes"] = stat.st_size
    return info


def _manifest_path(config: Any) -> Path:
    return config.authoritative_artifacts.index_dir / "manifest.json"


def _coverage_summary(report: dict[str, Any]) -> dict[str, Any]:
    summary = report.get("summary")
    if isinstance(summary, dict):
        graph_coverage = summary.get("graph_coverage")
        if isinstance(graph_coverage, dict):
            return graph_coverage
    coverage = report.get("coverage")
    return coverage if isinstance(coverage, dict) else {}


def main() -> int:
    args = parse_args()
    config = load_dag_toolchain_config(args.config)
    root = repo_root()
    manifest_path = _manifest_path(config)

    refresh_cmd = [
        sys.executable,
        "tools/infra/dag_refresh.py",
        "--config",
        repo_display_path(config.config_path, root),
    ]
    if args.run_mode:
        refresh_cmd.extend(["--run-mode", args.run_mode])
    if args.force:
        refresh_cmd.append("--force")
    if args.skip_prebuild:
        refresh_cmd.append("--skip-prebuild")

    print(f"[dag-manifest] config: {repo_display_path(config.config_path, root)}", flush=True)
    print(f"[dag-manifest] running: {' '.join(refresh_cmd)}", flush=True)
    print(f"[dag-manifest] manifest: {repo_display_path(manifest_path, root)}", flush=True)
    if args.dry_run:
        return 0

    refresh_result = subprocess.run(refresh_cmd, cwd=root)
    if refresh_result.returncode != 0:
        return refresh_result.returncode

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

    manifest = {
        "schemaVersion": MANIFEST_SCHEMA_VERSION,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "config": {
            "path": repo_display_path(config.config_path, root),
            "schemaVersion": config.schema_version,
        },
        "build": {
            "buildTarget": config.build.build_target,
            "importRoot": config.build.import_root,
            "namespaceFilter": config.build.namespace_filter,
            "runMode": args.run_mode or config.build.run_mode,
        },
        "refresh": {
            "forced": args.force,
            "skipPrebuild": args.skip_prebuild,
        },
        "artifacts": {
            "meta": _file_info(meta_path, root),
            "fullGraph": _file_info(config.authoritative_artifacts.graph_out, root),
            "structuralTopology": _file_info(config.authoritative_artifacts.structure_out, root),
        },
        "metaSummary": {
            "schemaVersion": meta.get("schemaVersion"),
            "timestamp": meta.get("timestamp"),
            "oleanHash": meta.get("oleanHash"),
            "nodeCount": meta.get("nodeCount"),
            "edgeCount": meta.get("edgeCount"),
            "morphismCount": meta.get("morphismCount"),
            "importRoot": meta.get("importRoot"),
            "namespaceFilter": meta.get("nsFilter"),
        },
        "derivedState": {
            "coverageReport": _file_info(config.derived_reports.coverage_report_json, root),
            "coverageSummary": _coverage_summary(coverage_report),
            "leakageReport": _file_info(config.policies.leakage.report_sidecar, root),
            "leakageSummary": {
                "droppedEdges": leakage_report.get("droppedEdges"),
                "dstOutsideModuleEdges": leakage_report.get("dstOutsideModuleEdges"),
                "dstInsideModuleGeneratedEdges": leakage_report.get("dstInsideModuleGeneratedEdges"),
                "dstInsideModuleStableEdges": leakage_report.get("dstInsideModuleStableEdges"),
                "dstUnknownEdges": leakage_report.get("dstUnknownEdges"),
            },
        },
    }

    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
