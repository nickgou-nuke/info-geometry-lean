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
                    "dag_meta": {
                        "schemaVersion": 3,
                        "nodeCount": 4,
                        "edgeCount": 3,
                        "morphismCount": 1,
                        "importRoot": "InfoGeometry.All",
                    },
                    "counts": {
                        "nodes": 4,
                        "edges": 3,
                        "depth_rows": 2,
                        "path_endpoints": {
                            "source": 1,
                            "sink": 1,
                            "internal": 1,
                            "isolated": 1,
                        },
                        "failed_transition_edges": 1,
                        "locked_edges": 0,
                        "duplicate_edges_removed": 0,
                    },
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
                        "attrs": {"path_endpoint": "source"},
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
                        "attrs": {"path_endpoint": "internal"},
                    },
                    {
                        "id": "InfoGeometry.Test.c",
                        "name": "InfoGeometry.Test.c",
                        "kind": "Declaration",
                        "module": "InfoGeometry.Test",
                        "file": "lean/InfoGeometry/Test.lean",
                        "line": 30,
                        "rep_depth": None,
                        "role": "owner",
                        "module_family": "InfoGeometry.Test",
                        "commit_sha": "abc123",
                        "toolchain": "leanprover/lean4:v4.28.0",
                        "artifact_version": 3,
                        "attrs": {"path_endpoint": "sink"},
                    },
                ],
                "edges": [
                    {"src": "InfoGeometry.Test.a", "dst": "InfoGeometry.Test.b", "kind": "DeclToDecl", "weight": 1.0, "evidence_ref": "e1", "attrs": {}},
                    {"src": "InfoGeometry.Test.b", "dst": "InfoGeometry.Test.c", "kind": "DeclToDecl", "weight": 1.0, "evidence_ref": "e2", "attrs": {}},
                    {"src": "module:InfoGeometry.Test", "dst": "InfoGeometry.Test.a", "kind": "ModuleToDecl", "weight": 1.0, "evidence_ref": "e3", "attrs": {}},
                ],
            },
            indent=2,
        ) + "\n",
        encoding="utf-8",
    )


def test_snapshot_summary_cli_json(tmp_path: Path) -> None:
    snapshot = tmp_path / "artifacts" / "leantrail" / "graph_snapshot.json"
    _write_snapshot(snapshot)

    out = subprocess.check_output(
        [
            sys.executable,
            str(ROOT / "tools" / "leantrail" / "snapshot_summary.py"),
            "--snapshot",
            str(snapshot),
        ],
        cwd=ROOT,
        text=True,
    )

    payload = json.loads(out)
    assert payload["counts"]["nodes"] == 4
    assert payload["node_kind_counts"] == {"Declaration": 3, "Module": 1}
    assert payload["edge_kind_counts"] == {"DeclToDecl": 2, "ModuleToDecl": 1}
    assert payload["metadata"]["commit_sha"] == "abc123"


def test_scripts_cli_exposes_leantrail_snapshot_command(tmp_path: Path) -> None:
    snapshot = tmp_path / "artifacts" / "leantrail" / "graph_snapshot.json"
    _write_snapshot(snapshot)

    out = subprocess.check_output(
        [
            sys.executable,
            "-m",
            "scripts.cli",
            "leantrail-snapshot",
            "--snapshot",
            str(snapshot),
            "--format",
            "text",
        ],
        cwd=ROOT,
        text=True,
    )

    assert "commit_sha=abc123" in out
    assert "nodes=4 edges=3" in out
    assert "node_kinds: Declaration=3, Module=1" in out
    assert "edge_kinds: DeclToDecl=2, ModuleToDecl=1" in out
