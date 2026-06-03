from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _write_snapshot(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "metadata": {
                    "created_at": "test",
                    "commit_sha": "test",
                    "toolchain": "test",
                    "artifact_version": 1,
                },
                "nodes": [
                    {
                        "id": "Suppressed.Alias",
                        "name": "Suppressed.Alias",
                        "kind": "Declaration",
                        "module": "InfoGeometry.Alias",
                        "file": "InfoGeometry/Alias.lean",
                        "line": 20,
                        "rep_depth": None,
                        "role": None,
                        "module_family": "InfoGeometry",
                        "commit_sha": "test",
                        "toolchain": "test",
                        "artifact_version": 1,
                        "attrs": {
                            "structural_dedup": {
                                "relation_type": "true_dedup_candidate",
                                "relation_subtype": "compatibility_alias_candidate",
                                "recommended_action": "review_as_alias_family",
                                "family_id": "family:alias",
                                "member_count": 3,
                            }
                        },
                    }
                ],
                "edges": [],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def test_scripts_cli_exposes_leantrail_dedup_command(tmp_path: Path) -> None:
    snapshot = tmp_path / "artifacts" / "leantrail" / "graph_snapshot.json"
    _write_snapshot(snapshot)

    out = subprocess.check_output(
        [
            sys.executable,
            "-m",
            "scripts.cli",
            "leantrail-dedup",
            "--snapshot",
            str(snapshot),
            "--status",
            "suppressed",
            "--format",
            "text",
        ],
        cwd=ROOT,
        text=True,
    )

    assert "status=suppressed" in out
    assert "Suppressed.Alias" in out
    assert "review_as_alias_family" in out
