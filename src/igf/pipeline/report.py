from __future__ import annotations

from pathlib import Path
from typing import Any

from igf.artifacts.io import count_jsonl_rows
from igf.artifacts.manifest import ARTIFACT_FILES


def report_artifacts(artifact_dir: Path) -> dict[str, Any]:
    counts = {name: count_jsonl_rows(artifact_dir / name) for name in ARTIFACT_FILES}
    manifest = artifact_dir / "manifest.json"
    return {
        "ok": True,
        "artifact_dir": str(artifact_dir),
        "manifest_present": manifest.exists(),
        "row_counts": counts,
    }

