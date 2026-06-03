from __future__ import annotations

from pathlib import Path

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.query_api import LeanTrailQueryAPI
from leantrail.backend.store import GraphStore


def _snapshot_with_dedup_statuses() -> GraphSnapshot:
    payload = {
        "metadata": {"created_at": "test", "commit_sha": "test", "toolchain": "test", "artifact_version": 1},
        "nodes": [
            {
                "id": "Active.Dedup",
                "name": "Active.Dedup",
                "kind": "Declaration",
                "module": "InfoGeometry.Active",
                "file": "InfoGeometry/Active.lean",
                "line": 10,
                "rep_depth": None,
                "role": None,
                "module_family": "InfoGeometry",
                "commit_sha": "test",
                "toolchain": "test",
                "artifact_version": 1,
                "attrs": {
                    "structural_dedup": {
                        "relation_type": "true_dedup_candidate",
                        "relation_subtype": "true_dedup_candidate",
                        "recommended_action": "review_for_contraction",
                        "family_id": "family:active",
                        "member_count": 2,
                    }
                },
            },
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
            },
            {
                "id": "No.Dedup",
                "name": "No.Dedup",
                "kind": "Declaration",
                "module": "InfoGeometry.Core",
                "file": "InfoGeometry/Core.lean",
                "line": 30,
                "rep_depth": None,
                "role": None,
                "module_family": "InfoGeometry",
                "commit_sha": "test",
                "toolchain": "test",
                "artifact_version": 1,
                "attrs": {},
            },
        ],
        "edges": [],
    }
    return GraphSnapshot.from_dict(payload)


def _api_with_store(tmp_path: Path) -> LeanTrailQueryAPI:
    api = LeanTrailQueryAPI(
        repo_root=tmp_path,
        snapshot_path=tmp_path / "graph_snapshot.json",
        bridge_dir=tmp_path / "bridge",
        bridge_schema_path=tmp_path / "bridge.schema.json",
    )
    api.store = GraphStore(_snapshot_with_dedup_statuses())
    return api


def test_dedup_candidates_defaults_to_active_only(tmp_path: Path) -> None:
    api = _api_with_store(tmp_path)

    result = api.dedup_candidates()

    assert result["status"] == "active"
    assert result["summary"] == {"active": 1, "suppressed": 1, "none": 1}
    assert [row["node"]["name"] for row in result["results"]] == ["Active.Dedup"]
    assert result["results"][0]["dedup_status"] == "active"


def test_dedup_candidates_can_query_suppressed_and_all(tmp_path: Path) -> None:
    api = _api_with_store(tmp_path)

    suppressed = api.dedup_candidates(status="suppressed")
    assert [row["node"]["name"] for row in suppressed["results"]] == ["Suppressed.Alias"]
    assert suppressed["results"][0]["dedup_status"] == "suppressed"

    all_rows = api.dedup_candidates(status="all")
    assert [row["node"]["name"] for row in all_rows["results"]] == ["Active.Dedup", "Suppressed.Alias"]
