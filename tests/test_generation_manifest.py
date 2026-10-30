from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.repository_evolution.generation_manifest import (
    _canonical_sha256,
    build_current_source_generation_manifest,
    validate_current_source_generation_manifest,
)
from tools.repository_evolution.git_fossil_overlay import _generation_id
from tools.repository_evolution.infotree_dna import (
    FEATURE_VERSION,
    capture_bundle_fingerprint,
)


def test_documented_script_path_entrypoint_loads_repository_imports():
    repository_root = Path(__file__).resolve().parents[1]
    script = repository_root / "tools/repository_evolution/generation_manifest.py"

    result = subprocess.run(
        [sys.executable, str(script), "--help"],
        cwd=repository_root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    assert "refactoring_map" in result.stdout


def _map(*paths: str) -> dict:
    files = []
    for index, path in enumerate(paths):
        files.append({
            "path": path,
            "role": "lean_source",
            "contentSha256": hashlib.sha256(path.encode()).hexdigest(),
            "buildTargets": [],
        })
    return {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "gitHead": "a" * 40,
            "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "b" * 64,
            "filesystemTopologySha256": "c" * 64,
        },
        "analysisProvenance": {
            "analysisInputsConsistentDuringScan": True,
            "scannerSourceSha256": "d" * 64,
            "lakeManifestSha256": "e" * 64,
        },
        "files": files,
    }


def _dna(source_map: dict, path: str) -> dict:
    source_sha = next(row["contentSha256"] for row in source_map["files"]
                      if row["path"] == path)
    features = {"node.kind=tactic": 3}
    context = "2" * 64
    row_hashes = {
        "raw_infotree_roots.jsonl": "0" * 64,
        "raw_infotree_nodes.jsonl": "1" * 64,
        "raw_infotree_projection_leakage.jsonl": "2" * 64,
    }
    raw_capture = capture_bundle_fingerprint(row_hashes)
    return {
        "schema": "info_geometry.infotree_structural_dna.v1",
        "featureVersion": FEATURE_VERSION,
        "artifactId": path,
        "sourceSha256": source_sha,
        "leanContextFingerprint": context,
        "exporterSourceSha256": "e" * 64,
        "rawRowFileSha256": row_hashes,
        "rawCaptureSha256": raw_capture,
        "features": features,
        "captureLossless": False,
        "leakageRowCount": 1,
        "status": "partial_structural_candidate_with_recorded_loss",
        "dnaFingerprint": _canonical_sha256({
            "featureVersion": FEATURE_VERSION,
            "sourceSha256": source_sha,
            "leanContextFingerprint": context,
            "exporterSourceSha256": "e" * 64,
            "rawCaptureSha256": raw_capture,
            "features": features,
        }),
    }


def test_generation_manifest_binds_source_inventory_and_dna_and_verifies():
    source_map = _map("lean/A.lean", "lean/B.lean")
    records = [_dna(source_map, "lean/A.lean"), _dna(source_map, "lean/B.lean")]
    manifest = build_current_source_generation_manifest(source_map, records)
    validate_current_source_generation_manifest(source_map, records, manifest)
    assert manifest["coverageStatus"] == "complete"
    assert manifest["expectedLeanSourceCount"] == manifest["capturedLeanSourceCount"] == 2
    assert manifest["manifestSha256"] == _canonical_sha256({
        key: value for key, value in manifest.items() if key != "manifestSha256"
    })
    assert manifest["partialCaptureCount"] == 2
    assert manifest["leakageRowCount"] == 2



@pytest.mark.parametrize("change", ["missing", "tampered", "legacy"])
def test_generation_rejects_unbound_or_tampered_exporter_receipt(change):
    source_map = _map("lean/A.lean")
    record = _dna(source_map, "lean/A.lean")
    if change == "missing":
        del record["exporterSourceSha256"]
    elif change == "tampered":
        record["exporterSourceSha256"] = "f" * 64
    else:
        record["featureVersion"] = "raw_infotree_structural_dna.v3"
    with pytest.raises(ValueError, match="exporter source|fingerprint does not verify|feature version"):
        build_current_source_generation_manifest(source_map, [record])


def test_missing_infotree_files_are_explicit_partial_coverage():
    source_map = _map("lean/A.lean", "lean/B.lean")
    records = [_dna(source_map, "lean/A.lean")]
    manifest = build_current_source_generation_manifest(source_map, records)
    assert manifest["coverageStatus"] == "partial_missing_captures"
    assert manifest["missingLeanSources"] == ["lean/B.lean"]
    assert manifest["coverageRatio"] == 0.5


def test_build_target_capture_coverage_handles_overlap_and_unowned_sources():
    source_map = _map("lean/A.lean", "lean/B.lean", "lean/Orphan.lean")
    source_map["files"][0]["buildTargets"] = ["Target.one", "Target.two"]
    source_map["files"][1]["buildTargets"] = ["Target.one"]
    records = [_dna(source_map, "lean/A.lean")]

    manifest = build_current_source_generation_manifest(source_map, records)
    coverage = manifest["lakeBuildTargetCaptureCoverage"]

    assert manifest["schema"] == "info_geometry.current_source_generation_manifest.v2"
    assert coverage["targets"] == {
        "Target.one": {
            "expectedSourceCount": 2,
            "capturedSourceCount": 1,
            "missingSourceCount": 1,
            "coverageRatio": 0.5,
        },
        "Target.two": {
            "expectedSourceCount": 1,
            "capturedSourceCount": 1,
            "missingSourceCount": 0,
            "coverageRatio": 1.0,
        },
    }
    assert coverage["sourcesWithoutBuildTargets"] == {
        "expectedSourceCount": 1,
        "capturedSourceCount": 0,
        "missingSourceCount": 1,
    }
    validate_current_source_generation_manifest(source_map, records, manifest)


def test_selected_source_scope_accepts_unrelated_scanner_changes_and_revalidates(tmp_path):
    source_map = _map("lean/A.lean", "lean/B.lean")
    source_map["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 1,
        "changedPathSampleDuringScan": ["docs/COUNTEREXAMPLE_INVENTORY_STATUS.md"],
    })
    for row in source_map["files"]:
        path = Path(row["path"])
        target = tmp_path / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(row["path"].encode())
    record = _dna(source_map, "lean/A.lean")

    manifest = build_current_source_generation_manifest(
        source_map, [record], scope_artifacts=["lean/A.lean"], repo_root=tmp_path,
    )
    validate_current_source_generation_manifest(
        source_map, [record], manifest, repo_root=tmp_path,
    )

    assert manifest["manifestScope"] == {
        "kind": "selected_lean_source_scope",
        "artifactIds": ["lean/A.lean"],
        "sourceSha256ByArtifact": {
            "lean/A.lean": source_map["files"][0]["contentSha256"],
        },
        "globalSnapshotConsistent": False,
        "changedPathsDuringScan": ["docs/COUNTEREXAMPLE_INVENTORY_STATUS.md"],
        "scopeDisjointFromChangedPaths": True,
    }
    assert manifest["expectedLeanSourceCount"] == 1
    assert manifest["capturedLeanSourceCount"] == 1
    assert manifest["coverageRatio"] == 1.0


def test_selected_source_scope_uses_complete_changed_paths_beyond_legacy_sample(tmp_path):
    source_map = _map("lean/A.lean", "lean/B.lean")
    changed_paths = [f"docs/churn-{index:02d}.md" for index in range(25)]
    source_map["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": len(changed_paths),
        "changedPathSampleDuringScan": changed_paths[:20],
        "changedPathsDuringScan": changed_paths,
        "changedPathSetSha256": hashlib.sha256(json.dumps(
            changed_paths, ensure_ascii=False, separators=(",", ":")
        ).encode()).hexdigest(),
    })
    for row in source_map["files"]:
        source = tmp_path / row["path"]
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes(row["path"].encode())

    record = _dna(source_map, "lean/A.lean")
    manifest = build_current_source_generation_manifest(
        source_map, [record], scope_artifacts=["lean/A.lean"], repo_root=tmp_path,
    )
    validate_current_source_generation_manifest(
        source_map, [record], manifest, repo_root=tmp_path,
    )

    assert manifest["manifestScope"]["changedPathsDuringScan"] == changed_paths
    assert manifest["manifestScope"]["scopeDisjointFromChangedPaths"] is True


def test_selected_source_scope_rejects_tampered_complete_changed_path_digest(tmp_path):
    source_map = _map("lean/A.lean")
    source_map["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 1,
        "changedPathSampleDuringScan": ["docs/README.md"],
        "changedPathsDuringScan": ["docs/README.md"],
        "changedPathSetSha256": "0" * 64,
    })
    source = tmp_path / "lean/A.lean"
    source.parent.mkdir(parents=True)
    source.write_bytes(source_map["files"][0]["path"].encode())

    with pytest.raises(ValueError, match="changed-path-set digest mismatch"):
        build_current_source_generation_manifest(
            source_map, [], scope_artifacts=["lean/A.lean"], repo_root=tmp_path,
        )


def test_selected_source_scope_fails_if_changed_path_set_is_incomplete_or_overlapping(tmp_path):
    source_map = _map("lean/A.lean")
    row = source_map["files"][0]
    source = tmp_path / row["path"]
    source.parent.mkdir(parents=True)
    source.write_bytes(row["path"].encode())
    source_map["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 2,
        "changedPathSampleDuringScan": ["docs/README.md"],
    })
    with pytest.raises(ValueError, match="omitted changed paths"):
        build_current_source_generation_manifest(
            source_map, [], scope_artifacts=[row["path"]], repo_root=tmp_path,
        )

    source_map["sourceSnapshot"].update({
        "changedPathCountDuringScan": 1,
        "changedPathSampleDuringScan": [row["path"]],
    })
    with pytest.raises(ValueError, match="intersects paths changed during scan"):
        build_current_source_generation_manifest(
            source_map, [], scope_artifacts=[row["path"]], repo_root=tmp_path,
        )


def test_selected_source_scope_rejects_live_hash_mismatch(tmp_path):
    source_map = _map("lean/A.lean")
    row = source_map["files"][0]
    source_map["sourceSnapshot"].update({
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 0,
        "changedPathSampleDuringScan": [],
    })
    source = tmp_path / row["path"]
    source.parent.mkdir(parents=True)
    source.write_text("changed after scan", encoding="utf-8")

    with pytest.raises(ValueError, match="selected source digest differs from map"):
        build_current_source_generation_manifest(
            source_map, [], scope_artifacts=[row["path"]], repo_root=tmp_path,
        )


@pytest.mark.parametrize(
    "owner_status, reason, summary_field",
    [
        ("uncertain_module_not_in_lake_target_index",
         "source_not_in_lake_target_index", "unindexedLeanSources"),
        ("uncertain_no_root_reachability",
         "module_not_reachable_from_lake_root", "unreachableLeanModules"),
    ],
)
def test_generation_manifest_distinguishes_unbuildable_source_coverage(
        owner_status, reason, summary_field):
    source_map = _map("lean/Unmapped.lean")
    source_map["files"][0]["ownerStatus"] = owner_status
    source_map["files"][0]["buildTargets"] = []

    manifest = build_current_source_generation_manifest(source_map, [])

    assert manifest[summary_field] == ["lean/Unmapped.lean"]
    assert manifest["captureAttemptAudit"]["missingSourceDiagnostics"][0][
        "reason"] == reason


def test_batch_failures_and_unextracted_successes_are_diagnostic_not_dna():
    source_map = _map("lean/A.lean", "lean/B.lean")
    accepted = [_dna(source_map, "lean/A.lean")]
    reports = [{
        "schema": "info_geometry.raw_infotree_batch_export_report.v1",
        "results": [
            {"file": "lean/A.lean", "status": "ok",
             "source_provenance": {
                 "sourceSha256": source_map["files"][0]["contentSha256"],
                 "leanContextFingerprint": "ctx-current",
             }},
            {"file": "lean/B.lean", "status": "ok",
             "source_provenance": {
                 "sourceSha256": source_map["files"][1]["contentSha256"],
                 "leanContextFingerprint": "ctx-exported",
             }},
            {"file": "lean/B.lean", "status": "timeout",
             "source_sha256": "0" * 64},
            {"file": "../other-checkout/lean/C.lean", "status": "ok"},
        ],
    }]

    manifest = build_current_source_generation_manifest(
        source_map, accepted, batch_reports=reports
    )
    audit = manifest["captureAttemptAudit"]
    assert manifest["capturedLeanSourceCount"] == 1
    assert audit["attemptCount"] == 3
    assert audit["attemptStatusCounts"] == {"ok": 2, "timeout": 1}
    assert audit["outOfInventoryAttemptCount"] == 1
    assert audit["missingSourcesWithAttempts"] == 1
    assert audit["missingSourceDiagnostics"] == [{
        "artifactId": "lean/B.lean",
        "reason": "export_succeeded_but_no_current_dna_record",
        "attempts": [
            {"reportedStatus": "ok", "sourceDigestMatch": True,
             "dnaAccepted": False,
             "captureContextFingerprint": "ctx-exported"},
            {"reportedStatus": "timeout", "sourceDigestMatch": False,
             "dnaAccepted": False},
        ],
    }]


def test_stale_olean_rejection_is_propagated_as_missing_capture_reason():
    source_map = _map("lean/A.lean")
    report = {
        "schema": "info_geometry.infotree_dna_rejection_report.v1",
        "rejectionCount": 1,
        "rejections": [{
            "artifactId": "lean/A.lean",
            "reason": "stale_lean_context",
            "reportedSourceSha256": source_map["files"][0]["contentSha256"],
        }],
    }
    manifest = build_current_source_generation_manifest(
        source_map, [], rejection_reports=[report]
    )
    audit = manifest["captureAttemptAudit"]
    assert audit["rejectedCaptureCount"] == 1
    assert audit["rejectionReasonCounts"] == {"stale_lean_context": 1}
    assert audit["missingSourceDiagnostics"][0]["reason"] == "lean_context_rejected"


@pytest.mark.parametrize("mutation, message", [
    ("source", "source digest differs"),
    ("fingerprint", "fingerprint does not verify"),
    ("schema", "schema"),
    ("feature", "feature version"),
    ("roots_digest", "missing its required roots-file digest"),
    ("leakage_digest", "missing its required projection-leakage digest"),
    ("capture_bundle", "raw-capture fingerprint does not match"),
    ("context_hash", "invalid Lean context fingerprint"),
    ("loss_status", "status disagrees with capture-loss evidence"),
])
def test_generation_manifest_rejects_unbound_or_invalid_dna(mutation, message):
    source_map = _map("lean/A.lean")
    record = _dna(source_map, "lean/A.lean")
    if mutation == "source":
        record["sourceSha256"] = "0" * 64
    elif mutation == "fingerprint":
        record["dnaFingerprint"] = "0" * 64
    elif mutation == "schema":
        record["schema"] = "other"
    elif mutation == "feature":
        record["featureVersion"] = "future-unknown"
    elif mutation == "capture_bundle":
        record["rawRowFileSha256"]["raw_infotree_nodes.jsonl"] = "9" * 64
    elif mutation == "roots_digest":
        del record["rawRowFileSha256"]["raw_infotree_roots.jsonl"]
        record["rawCaptureSha256"] = capture_bundle_fingerprint(record["rawRowFileSha256"])
        record["dnaFingerprint"] = _canonical_sha256({
            "featureVersion": FEATURE_VERSION,
            "sourceSha256": record["sourceSha256"],
            "leanContextFingerprint": record["leanContextFingerprint"],
            "exporterSourceSha256": record["exporterSourceSha256"],
            "rawCaptureSha256": record["rawCaptureSha256"],
            "features": record["features"],
        })
    elif mutation == "leakage_digest":
        del record["rawRowFileSha256"]["raw_infotree_projection_leakage.jsonl"]
        record["rawCaptureSha256"] = capture_bundle_fingerprint(record["rawRowFileSha256"])
        record["dnaFingerprint"] = _canonical_sha256({
            "featureVersion": FEATURE_VERSION,
            "sourceSha256": record["sourceSha256"],
            "leanContextFingerprint": record["leanContextFingerprint"],
            "exporterSourceSha256": record["exporterSourceSha256"],
            "rawCaptureSha256": record["rawCaptureSha256"],
            "features": record["features"],
        })
    elif mutation == "context_hash":
        record["leanContextFingerprint"] = "not-a-sha256"
    else:
        record["status"] = "structural_dna_candidate"
    with pytest.raises(ValueError, match=message):
        build_current_source_generation_manifest(source_map, [record])


def test_generation_manifest_rejects_duplicates_and_non_lean_dna():
    source_map = _map("lean/A.lean")
    record = _dna(source_map, "lean/A.lean")
    with pytest.raises(ValueError, match="duplicate InfoTree DNA"):
        build_current_source_generation_manifest(source_map, [record, record])
    other = _dna(source_map, "lean/A.lean")
    other["artifactId"] = "src/not-lean.py"
    with pytest.raises(ValueError, match="non-current Lean source"):
        build_current_source_generation_manifest(source_map, [other])


def test_manifest_verification_detects_stale_source_map():
    source_map = _map("lean/A.lean")
    records = [_dna(source_map, "lean/A.lean")]
    manifest = build_current_source_generation_manifest(source_map, records)
    changed = _map("lean/A.lean")
    changed["files"][0]["contentSha256"] = "0" * 64
    with pytest.raises(ValueError, match="source digest differs"):
        validate_current_source_generation_manifest(changed, records, manifest)


def test_generation_manifest_binds_the_optional_git_fossil_overlay():
    source_map = _map("lean/A.lean")
    records = [_dna(source_map, "lean/A.lean")]
    generation_id = _generation_id(source_map["sourceSnapshot"],
                                   source_map["analysisProvenance"])
    lineage_features = {"lean/A.lean": {
        "schema": "info_geometry.source_lineage_features.v1",
        "generationId": generation_id,
        "historyRevision": source_map["sourceSnapshot"]["gitHead"],
        "sourcePath": "lean/A.lean",
        "sourceSha256": records[0]["sourceSha256"],
    }}
    overlay = {
        "schema": "info_geometry.git_fossil_overlay_manifest.v1",
        "generationId": generation_id,
        "gitHead": source_map["sourceSnapshot"]["gitHead"],
        "pathContentManifestSha256": source_map["sourceSnapshot"][
            "pathContentManifestSha256"],
        "sourceCount": 1,
        "gitPathEventsSha256": "2" * 64,
        "gitPathEventCount": 5,
        "nodeLinksSha256": "3" * 64,
        "sourceLineFossilsSha256": "4" * 64,
        "sourceLineFossilSpanCount": 0,
        "declarationLineFossilLinksSha256": "5" * 64,
        "declarationLineFossilLinkCount": 0,
        "declarationLineFossilEdgeCount": 0,
        "sourceLineageFeaturesByPath": lineage_features,
        "sourceLineageFeaturesSha256": _canonical_sha256(lineage_features),
        "nodeLinkCount": 7,
    }
    manifest = build_current_source_generation_manifest(source_map, records, overlay)
    validate_current_source_generation_manifest(source_map, records, manifest, overlay)
    assert manifest["gitFossilOverlay"]["nodeLinkCount"] == 7
    changed = {**overlay, "gitHead": "4" * 40}
    with pytest.raises(ValueError, match="different HEAD"):
        build_current_source_generation_manifest(source_map, records, changed)
