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
                    "created_at": "2026-06-02T00:00:00Z",
                    "source": "leantrail.normalizer",
                    "commit_sha": "abc123",
                    "toolchain": "leanprover/lean4:v4.28.0",
                    "artifact_version": 3,
                },
                "nodes": [
                    {
                        "id": "module:InfoGeometry.Test",
                        "name": "InfoGeometry.Test",
                        "kind": "Module",
                        "module": "InfoGeometry.Test",
                        "file": None,
                        "line": None,
                        "rep_depth": None,
                        "role": "owner",
                        "module_family": "InfoGeometry.Test",
                        "commit_sha": "abc123",
                        "toolchain": "leanprover/lean4:v4.28.0",
                        "artifact_version": 3,
                        "attrs": {},
                    },
                    {
                        "id": "InfoGeometry.Test.a",
                        "name": "InfoGeometry.Test.a",
                        "kind": "Declaration",
                        "module": "InfoGeometry.Test",
                        "file": "lean/InfoGeometry/Test.lean",
                        "line": 10,
                        "rep_depth": None,
                        "role": "owner",
                        "module_family": "InfoGeometry.Test",
                        "commit_sha": "abc123",
                        "toolchain": "leanprover/lean4:v4.28.0",
                        "artifact_version": 3,
                        "attrs": {"decl_kind": "theorem", "path_endpoint": "source"},
                    },
                    {
                        "id": "InfoGeometry.Test.b",
                        "name": "InfoGeometry.Test.b",
                        "kind": "Declaration",
                        "module": "InfoGeometry.Test",
                        "file": "lean/InfoGeometry/Test.lean",
                        "line": 20,
                        "rep_depth": None,
                        "role": "owner",
                        "module_family": "InfoGeometry.Test",
                        "commit_sha": "abc123",
                        "toolchain": "leanprover/lean4:v4.28.0",
                        "artifact_version": 3,
                        "attrs": {"decl_kind": "def", "path_endpoint": "sink"},
                    },
                ],
                "edges": [
                    {"src": "module:InfoGeometry.Test", "dst": "InfoGeometry.Test.a", "kind": "contains", "weight": 1.0, "evidence_ref": "e1", "attrs": {}},
                    {"src": "InfoGeometry.Test.a", "dst": "InfoGeometry.Test.b", "kind": "depends_value", "weight": 1.0, "evidence_ref": "e2", "attrs": {}},
                ],
            },
            indent=2,
        ) + "\n",
        encoding="utf-8",
    )


def test_decl_cli_json_exact_lookup(tmp_path: Path) -> None:
    snapshot = tmp_path / "artifacts" / "leantrail" / "graph_snapshot.json"
    _write_snapshot(snapshot)

    out = subprocess.check_output(
        [
            sys.executable,
            str(ROOT / "tools" / "leantrail" / "decl_lookup.py"),
            "--snapshot",
            str(snapshot),
            "--name",
            "InfoGeometry.Test.a",
        ],
        cwd=ROOT,
        text=True,
    )

    payload = json.loads(out)
    assert payload["node"]["name"] == "InfoGeometry.Test.a"
    assert payload["node"]["attrs"]["decl_kind"] == "theorem"
    assert payload["incoming"][0]["kind"] == "contains"
    assert payload["outgoing"][0]["kind"] == "depends_value"


def test_scripts_cli_exposes_leantrail_decl_command(tmp_path: Path) -> None:
    snapshot = tmp_path / "artifacts" / "leantrail" / "graph_snapshot.json"
    _write_snapshot(snapshot)

    out = subprocess.check_output(
        [
            sys.executable,
            "-m",
            "scripts.cli",
            "leantrail-decl",
            "--snapshot",
            str(snapshot),
            "--name",
            "InfoGeometry.Test.a",
            "--format",
            "text",
        ],
        cwd=ROOT,
        text=True,
    )

    assert "name=InfoGeometry.Test.a" in out
    assert "kind=Declaration module=InfoGeometry.Test line=10" in out
    assert "decl_kind=theorem" in out
    assert "incoming_edges=1 outgoing_edges=1" in out
