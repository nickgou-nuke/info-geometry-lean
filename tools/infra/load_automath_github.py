#!/usr/bin/env python3
"""
Faithful Automath Omega loader from the synced GitHub mirror.

This module does NOT confabulate theorems. It:
- reads the manifest produced by sync_automath_github.py
- copies a selected subset of the upstream Lean4 mirror into repo-local surfaces
  currently: lean/Omega and lean/InfoGeometry/External/Automath/Omega
- preserves local edits unless explicitly overridden
- emits a JSON load report for downstream pipeline stages
"""

import json
import shutil
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST_PATH = REPO_ROOT / "docs" / "automath_github_manifest.json"
UPSTREAM_LEAN4 = REPO_ROOT / "external_refs" / "automath" / "lean4"
TARGET_OMEGA = REPO_ROOT / "lean" / "Omega"
TARGET_EXTERNAL_AUTOMATH_OMEGA = (
    REPO_ROOT / "lean" / "InfoGeometry" / "External" / "Automath" / "Omega"
)
LOAD_REPORT_PATH = REPO_ROOT / "docs" / "automath_github_load_report.json"


@dataclass
class LoadReport:
    manifest_commit: Optional[str]
    upstream_lean4_exists: bool
    targets: dict[str, dict]
    loaded_at_utc: str

    def to_dict(self) -> dict:
        return {
            "manifest_commit": self.manifest_commit,
            "upstream_lean4_exists": self.upstream_lean4_exists,
            "targets": self.targets,
            "loaded_at_utc": self.loaded_at_utc,
        }


def _load_manifest() -> dict:
    if not MANIFEST_PATH.exists():
        raise FileNotFoundError(
            f"manifest not found: {MANIFEST_PATH}. Run sync_automath_github.py first."
        )
    return json.loads(MANIFEST_PATH.read_text())


def _copy_subset(
    src_root: Path,
    dst_root: Path,
    *,
    allow_overwrite: bool = False,
) -> dict:
    summary = {
        "src": str(src_root.relative_to(REPO_ROOT)),
        "dst": str(dst_root.relative_to(REPO_ROOT)),
        "allow_overwrite": allow_overwrite,
        "copied": 0,
        "skipped": 0,
        "missing_src": 0,
        "missing_dst_parents": 0,
        "files": [],
    }
    if not src_root.exists():
        summary["missing_src"] = 1
        return summary

    lean_files = sorted(src_root.rglob("*.lean"))
    for src in lean_files:
        rel = src.relative_to(src_root)
        dst = dst_root / rel
        if not dst.parent.exists():
            dst.parent.mkdir(parents=True, exist_ok=True)
            summary["missing_dst_parents"] += 1
        if dst.exists() and not allow_overwrite:
            summary["skipped"] += 1
            summary["files"].append({"file": str(rel), "action": "skipped"})
            continue
        shutil.copy2(src, dst)
        summary["copied"] += 1
        summary["files"].append({"file": str(rel), "action": "copied"})
    return summary


def load_automath_omega(
    *,
    copy_to_omega: bool = True,
    copy_to_external_automath_omega: bool = True,
    allow_overwrite: bool = False,
) -> LoadReport:
    manifest = _load_manifest()
    loaded_at = datetime.now(timezone.utc).isoformat()
    manifest_commit = (
        manifest.get("post_manifest") or manifest.get("pre_manifest") or {}
    ).get("commit")

    targets = {}
    if copy_to_omega:
        targets["lean/Omega"] = _copy_subset(
            UPSTREAM_LEAN4 / "Omega",
            TARGET_OMEGA,
            allow_overwrite=allow_overwrite,
        )
    if copy_to_external_automath_omega:
        targets["lean/InfoGeometry/External/Automath/Omega"] = _copy_subset(
            UPSTREAM_LEAN4 / "Omega",
            TARGET_EXTERNAL_AUTOMATH_OMEGA,
            allow_overwrite=allow_overwrite,
        )

    report = LoadReport(
        manifest_commit=manifest_commit,
        upstream_lean4_exists=UPSTREAM_LEAN4.exists(),
        targets=targets,
        loaded_at_utc=loaded_at,
    )
    LOAD_REPORT_PATH.write_text(json.dumps(report.to_dict(), indent=2) + "\n")
    return report


def main() -> int:
    report = load_automath_omega(allow_overwrite=False)
    print(json.dumps(report.to_dict(), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
