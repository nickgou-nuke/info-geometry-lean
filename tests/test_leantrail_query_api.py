from __future__ import annotations

import json
from pathlib import Path

from leantrail.backend import query_api
from leantrail.backend.models import EdgeRecord
from leantrail.backend.normalizer import _dedupe_edges
from leantrail.backend.query_api import LeanTrailQueryAPI


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _snapshot_payload(*, commit_sha: str, dag_meta: dict, decl_name: str) -> dict:
    return {
        "metadata": {
            "created_at": "test",
            "commit_sha": commit_sha,
            "toolchain": "test",
            "artifact_version": 1,
            "dag_meta": dag_meta,
        },
        "nodes": [
            {
                "id": decl_name,
                "name": decl_name,
                "kind": "Declaration",
                "module": "Test.Module",
                "file": "Test/Module.lean",
                "line": 42,
                "rep_depth": None,
                "role": None,
                "module_family": "Test",
                "commit_sha": commit_sha,
                "toolchain": "test",
                "artifact_version": 1,
                "attrs": {},
            }
        ],
        "edges": [],
    }


def test_snapshot_is_stale_when_dag_meta_or_commit_drift(tmp_path: Path, monkeypatch) -> None:
    repo_root = tmp_path
    snapshot_path = repo_root / "artifacts" / "leantrail" / "graph_snapshot.json"
    dag_meta_path = repo_root / "artifacts" / "dag" / "index" / "meta.json"

    stale_dag_meta = {
        "timestamp": "2026-05-16T05:11:39.711458+00:00",
        "sourceHash": "source-old",
        "oleanHash": "olean-old",
        "nodeCount": 1,
        "edgeCount": 2,
        "morphismCount": 3,
    }
    fresh_dag_meta = {
        "timestamp": "2026-06-01T19:00:09.446915+00:00",
        "sourceHash": "source-new",
        "oleanHash": "olean-new",
        "nodeCount": 10,
        "edgeCount": 20,
        "morphismCount": 30,
    }

    _write_json(snapshot_path, _snapshot_payload(commit_sha="old-commit", dag_meta=stale_dag_meta, decl_name="Test.Old"))
    _write_json(dag_meta_path, fresh_dag_meta)

    monkeypatch.setattr(query_api, "_safe_git_head", lambda _: "new-commit")

    assert query_api._snapshot_is_stale(repo_root, snapshot_path) is True


def test_ensure_loaded_rebuilds_stale_snapshot_before_serving_decl(tmp_path: Path, monkeypatch) -> None:
    repo_root = tmp_path
    snapshot_path = repo_root / "artifacts" / "leantrail" / "graph_snapshot.json"
    dag_meta_path = repo_root / "artifacts" / "dag" / "index" / "meta.json"
    bridge_dir = repo_root / "handover" / "injections"
    bridge_schema_path = repo_root / "schemas" / "bridge.schema.json"

    stale_dag_meta = {
        "timestamp": "2026-05-16T05:11:39.711458+00:00",
        "sourceHash": "source-old",
        "oleanHash": "olean-old",
        "nodeCount": 1,
        "edgeCount": 2,
        "morphismCount": 3,
    }
    fresh_dag_meta = {
        "timestamp": "2026-06-01T19:00:09.446915+00:00",
        "sourceHash": "source-new",
        "oleanHash": "olean-new",
        "nodeCount": 10,
        "edgeCount": 20,
        "morphismCount": 30,
    }

    _write_json(snapshot_path, _snapshot_payload(commit_sha="old-commit", dag_meta=stale_dag_meta, decl_name="Test.StaleDecl"))
    _write_json(dag_meta_path, fresh_dag_meta)
    _write_json(bridge_schema_path, {})
    bridge_dir.mkdir(parents=True, exist_ok=True)

    monkeypatch.setattr(query_api, "_safe_git_head", lambda _: "new-commit")

    rebuild_calls: list[tuple[Path, Path]] = []

    def fake_build_snapshot(repo_root_arg: Path, snapshot_path_arg: Path) -> Path:
        rebuild_calls.append((repo_root_arg, snapshot_path_arg))
        _write_json(
            snapshot_path_arg,
            _snapshot_payload(
                commit_sha="new-commit",
                dag_meta=fresh_dag_meta,
                decl_name="Test.FreshDecl",
            ),
        )
        return snapshot_path_arg

    monkeypatch.setattr(query_api, "build_snapshot", fake_build_snapshot)

    api = LeanTrailQueryAPI(
        repo_root=repo_root,
        snapshot_path=snapshot_path,
        bridge_dir=bridge_dir,
        bridge_schema_path=bridge_schema_path,
    )

    result = api.decl("Test.FreshDecl")

    assert len(rebuild_calls) == 1
    assert rebuild_calls[0] == (repo_root, snapshot_path)
    assert result["found"] is True
    assert result["node"]["name"] == "Test.FreshDecl"
    assert query_api._snapshot_is_stale(repo_root, snapshot_path) is False


def test_normalizer_dedupes_semantic_edge_wires() -> None:
    edges = [
        EdgeRecord(
            src="A",
            dst="B",
            kind="violates_depth",
            weight=3.0,
            evidence_ref="depth-a",
            attrs={},
        ),
        EdgeRecord(
            src="A",
            dst="B",
            kind="violates_depth",
            weight=2.0,
            evidence_ref="depth-b",
            attrs={"source": "secondary"},
        ),
        EdgeRecord(
            src="A",
            dst="B",
            kind="depends_value",
            weight=1.0,
            evidence_ref="dep",
            attrs={},
        ),
    ]

    deduped, removed = _dedupe_edges(edges)

    assert removed == 1
    assert len(deduped) == 2
    depth_edge = next(edge for edge in deduped if edge.kind == "violates_depth")
    assert depth_edge.weight == 3.0
    assert depth_edge.attrs["source"] == "secondary"
    assert depth_edge.attrs["evidence_refs"] == ["depth-a", "depth-b"]
