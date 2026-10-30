from __future__ import annotations

import hashlib
from pathlib import Path

import pytest

from tools.repository_evolution.taxonomy_adjudication_queue import (
    _owner_group,
    build_adjudication_queue,
)


def _fixture(tmp_path: Path):
    sources = {
        "lean/A.lean": ("theorem alpha : True := True.intro\n", "lean_source", "Lean.A"),
        "lean/B.lean": ("def beta : Nat := 2\n", "lean_source", "Lean.B"),
        "tools/C.py": ("def gamma():\n    return 3\n", "repository_evolution_analysis", None),
        "assets/D.bin": ("opaque".encode(), "non_source_asset", None),
    }
    files = []
    declarations = []
    for path, (source, role, module) in sources.items():
        full_path = tmp_path / path
        full_path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(source, str):
            source = source.encode()
        full_path.write_bytes(source)
        digest = hashlib.sha256(source).hexdigest()
        files.append({"path": path, "contentSha256": digest, "role": role,
                      "module": module, "owner": "Root", "sizeBytes": len(source),
                      "buildTargets": ["Root"] if module else []})
        if path == "lean/A.lean":
            declarations.append({"sourcePath": path, "kind": "theorem", "name": "alpha",
                                 "line": 1})
    report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {"worktreeConsistentDuringScan": True,
                           "pathContentManifestSha256": "snapshot-a"},
        "analysisProvenance": {"analysisInputsConsistentDuringScan": True,
                               "scannerSourceSha256": "b" * 64,
                               "lakeManifestSha256": "c" * 64},
        "files": files,
        "dependencyEdges": [{"from": "lean/A.lean", "to": "lean/B.lean",
                             "kind": "lean_source_import"}],
        "leanDeclarationCandidates": declarations,
    }
    return report


def test_review_sampling_groups_unindexed_modules_without_pseudo_owner_collapse():
    first = {
        "path": "lean/audit/AuditNative.lean",
        "moduleCandidate": "AuditNative",
        "moduleCandidateSourceRoot": "lean",
        "owner": "unresolved_lean_module",
        "ownerStatus": "uncertain_module_not_in_lake_target_index",
    }
    same_module = {**first, "path": "lean/other/AuditNative.lean"}
    other_module = {**first, "path": "lean/other/AuditStrict.lean",
                    "moduleCandidate": "AuditStrict"}
    no_module_candidate = {"path": "lean/other/Unknown.lean",
                           "owner": "unresolved_lean_module",
                           "ownerStatus": "uncertain_module_not_in_lake_target_index"}
    assert _owner_group(first) == _owner_group(same_module)
    assert _owner_group(first) != _owner_group(other_module)
    assert _owner_group(no_module_candidate) == "directory:lean/other"


def test_queue_is_deterministic_stratified_and_leaves_labels_unassigned(tmp_path: Path):
    report = _fixture(tmp_path)
    report["files"][0].update({
        "moduleCandidate": "Lean.A",
        "moduleCandidateSourceRoot": "lean",
        "moduleCandidateStatus": "lexical_source_root_candidate_not_lake_indexed",
    })
    tasks, manifest = build_adjudication_queue(report, tmp_path, limit=3,
                                               max_per_owner=1, seed="review-test")
    repeated, repeated_manifest = build_adjudication_queue(
        report, tmp_path, limit=3, max_per_owner=1, seed="review-test"
    )
    assert tasks == repeated
    assert manifest == repeated_manifest
    assert manifest["selectedArtifactCount"] == 3
    assert manifest["taskCount"] == 6
    assert {task["facet"] for task in tasks} == {"artifact_role", "semantic_archetype"}
    assert all(task["labels"] == [] and task["labelSetComplete"] is None for task in tasks)
    assert all(task["reviewStatus"] == "pending_human_adjudication" for task in tasks)
    assert all(task["sourceSha256"] for task in tasks)
    assert all(task["candidateEvidence"] for task in tasks)
    assert all(task["candidateEvidence"] for task in tasks if task["artifactId"] == "lean/A.lean")
    full_tasks, _ = build_adjudication_queue(report, tmp_path, limit=4, seed="review-test")
    selected_a = next(task for task in full_tasks if task["artifactId"] == "lean/A.lean")
    assert selected_a["observedContext"]["moduleCandidate"] == "Lean.A"
    assert selected_a["observedContext"]["moduleCandidateSourceRoot"] == "lean"
    assert set(manifest["signatureVocabularyReferenceOnly"][0]) == {"name", "signature"}
    assert max(manifest["selectedSamplingGroups"].values()) <= 1


def test_stable_partial_inventory_is_not_reported_as_whole_worktree(tmp_path: Path):
    report = _fixture(tmp_path)
    report["sourceSnapshot"].update({
        "inventoryScope": "explicit_path_selection",
        "worktreeConsistentDuringScan": True,
    })
    tasks, manifest = build_adjudication_queue(
        report, tmp_path, limit=2, seed="partial-inventory"
    )
    assert manifest["schema"] == "info_geometry.taxonomy_adjudication_queue_manifest.v2"
    assert manifest["sourceSnapshotConsistency"]["inventoryScope"] == "explicit_path_selection"
    assert manifest["sourceSnapshotConsistency"]["inventoryConsistentDuringScan"] is True
    assert manifest["sourceSnapshotConsistency"]["wholeWorktreeConsistentDuringScan"] is False
    assert manifest["sourceSnapshotConsistency"]["status"] == "selected_inventory_paths_consistent"
    assert all(task["schema"] == "info_geometry.taxonomy_adjudication_task.v2" for task in tasks)
    assert all(task["sourceSnapshotStatus"] == "selected_inventory_paths_consistent"
               for task in tasks)
    assert all(task["observedContext"]["dependencyContextStatus"] ==
               "partial_inventory_consistent_dependency_context_truncated" for task in tasks)


def test_stable_legacy_map_with_unknown_inventory_scope_is_not_called_inconsistent(
    tmp_path: Path,
):
    report = _fixture(tmp_path)
    tasks, manifest = build_adjudication_queue(
        report, tmp_path, limit=2, seed="legacy-unknown-scope"
    )
    expected = "inventory_scope_unspecified_selected_sources_hash_verified"
    assert manifest["sourceSnapshotConsistency"]["status"] == expected
    assert manifest["sourceSnapshotConsistency"]["inventoryScope"] == \
        "unspecified_inventory_scope"
    assert manifest["sourceSnapshotConsistency"]["wholeWorktreeConsistentDuringScan"] is False
    assert all(task["sourceSnapshotStatus"] == expected for task in tasks)
    assert all(task["observedContext"]["dependencyContextStatus"] ==
               "inventory_scope_unspecified_dependency_context_scope_unknown" for task in tasks)


def test_queue_rejects_inconsistent_maps_and_changed_selected_source(tmp_path: Path):
    report = _fixture(tmp_path)
    inconsistent = {**report, "sourceSnapshot": {
        **report["sourceSnapshot"], "worktreeConsistentDuringScan": False,
    }}
    with pytest.raises(ValueError, match="inconsistent source snapshot"):
        build_adjudication_queue(inconsistent, tmp_path)
    with pytest.raises(ValueError, match="positive integer"):
        build_adjudication_queue(report, tmp_path, limit=0)

    # The deterministic seed selects the same path every time; mutate a likely
    # selected source and require source binding to reject it.
    tasks, _ = build_adjudication_queue(report, tmp_path, limit=4, seed="stale")
    selected_path = tasks[0]["artifactId"]
    (tmp_path / selected_path).write_text("changed after map scan\n", encoding="utf-8")
    with pytest.raises(ValueError, match="selected source changed"):
        build_adjudication_queue(report, tmp_path, limit=4, seed="stale")


def test_scoped_queue_excludes_reported_changes_and_marks_mixed_edges(tmp_path: Path):
    report = _fixture(tmp_path)
    report["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 1,
        "changedPathSampleDuringScan": ["lean/A.lean"],
    })
    tasks, manifest = build_adjudication_queue(
        report, tmp_path, limit=3, seed="scoped-review",
        allow_scoped_review=True,
    )
    selected_paths = manifest["sourceSnapshotConsistency"]["selectedSourcePaths"]
    assert "lean/A.lean" not in selected_paths
    assert manifest["candidateArtifactCount"] == 4
    assert manifest["candidateArtifactCountAfterChangedPathExclusion"] == 3
    assert manifest["sourceSnapshotConsistency"]["wholeWorktreeConsistentDuringScan"] is False
    assert manifest["sourceSnapshotConsistency"]["selectedSourceHashesMatchMapAtQueueTime"] is True
    b_task = next(task for task in tasks if task["artifactId"] == "lean/B.lean")
    assert b_task["sourceSnapshotStatus"] == "selected_source_hash_verified_from_inconsistent_map"
    assert b_task["observedContext"]["dependencyContextStatus"] == \
        "map_edges_from_scoped_scan_require_caution"
    assert b_task["observedContext"]["changedDependencyNeighbors"] == ["lean/A.lean"]


def test_scoped_queue_rejects_incomplete_changed_path_inventory(tmp_path: Path):
    report = _fixture(tmp_path)
    report["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 2,
        "changedPathSampleDuringScan": ["lean/A.lean"],
    })
    with pytest.raises(ValueError, match="every changed path"):
        build_adjudication_queue(
            report, tmp_path, allow_scoped_review=True,
        )


def test_scoped_queue_skips_sources_that_changed_after_map_scan(tmp_path: Path):
    report = _fixture(tmp_path)
    selected_before, _ = build_adjudication_queue(
        report, tmp_path, limit=4, seed="late-change",
    )
    changed_artifact = selected_before[0]["artifactId"]
    (tmp_path / changed_artifact).write_text("changed after map scan\n", encoding="utf-8")
    report["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 0,
        "changedPathSampleDuringScan": [],
    })
    tasks, manifest = build_adjudication_queue(
        report, tmp_path, limit=4, seed="late-change",
        allow_scoped_review=True,
    )
    assert changed_artifact not in manifest["sourceSnapshotConsistency"]["selectedSourcePaths"]
    assert manifest["staleOrMissingSourceCandidateCount"] >= 1
    assert changed_artifact in manifest["staleOrMissingSourcePaths"]
    assert all(task["sourceSha256"] for task in tasks)
