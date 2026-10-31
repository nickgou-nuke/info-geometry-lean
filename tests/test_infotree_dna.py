"""Streaming, provenance-bound InfoTree structural DNA extraction tests."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import pytest

from tools.repository_evolution.infotree_dna import (
    compute_multiscale_dna_affinity_clusters,
    extract_one,
    extract_tree,
    extract_tree_audited,
)


def test_standalone_entrypoint_resolves_repository_imports(tmp_path):
    script = Path(__file__).resolve().parents[1] / "tools/repository_evolution/infotree_dna.py"
    result = subprocess.run(
        [sys.executable, "-I", "-c",
         "import runpy, sys; runpy.run_path(sys.argv[1]); "
         "from tools.build_lock import acquire_build_lock; "
         "from tools.infra.pantograph_environment import build_lean_context_manifest",
         str(script)],
        cwd=tmp_path, capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def _exporter_receipt(root: Path) -> str:
    exporter = root / "lean/DAG/RawInfoTreeExport.lean"
    exporter.parent.mkdir(parents=True, exist_ok=True)
    exporter.write_text("-- fixture exporter\n")
    return hashlib.sha256(exporter.read_bytes()).hexdigest()


def _fixture(root: Path, export: Path) -> Path:
    source = root / "lean" / "DAG" / "Basic.lean"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("def sample := 1\n", encoding="utf-8")
    export.mkdir(parents=True)
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    (export / "metadata.json").write_text(json.dumps({
        "schema": "info_geometry.raw_infotree_export.v1",
        "stage": "stage_4_deep_semantic_audit",
        "module": "lean.DAG.Basic",
        "fully_lossless": False,
        "loss_audited": True,
        "leakage_count": 1,
        "sourceProvenance": {
            "sourcePath": "lean/DAG/Basic.lean",
            "exporterSourceSha256": _exporter_receipt(root),
            "sourceSha256": source_sha,
            "leanContextFingerprint": "context-hash",
        },
    }), encoding="utf-8")
    _write_jsonl(export / "raw_infotree_roots.jsonl", [{
        "rootKey": "root-1", "file": "lean/DAG/Basic.lean", "module": "lean.DAG.Basic",
    }])
    _write_jsonl(export / "raw_infotree_nodes.jsonl", [
        {"kind": "tactic", "depth": 3, "branchingFactor": 2, "isLogical": True,
         "declName": "Hidden.theoremName"},
        {"kind": "command", "depth": 0, "branchingFactor": 1, "isLogical": False},
    ])
    _write_jsonl(export / "raw_infotree_edges.jsonl", [{"siblingIndex": 0}])
    _write_jsonl(export / "raw_infotree_contexts.jsonl", [{"contextKind": "tacticCtx"}])
    _write_jsonl(export / "raw_infotree_payload_fields.jsonl", [{
        "field": "goalsBefore", "value": "source text intentionally ignored",
    }])
    _write_jsonl(export / "raw_infotree_projection_leakage.jsonl", [{
        "field": "term_expr_graph", "reason": "serializer has no Expr graph projection",
    }])
    return source


def test_extract_one_emits_compact_features_without_names_or_values():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": hashlib.sha256(
                (root / "lean/DAG/Basic.lean").read_bytes()
            ).hexdigest(), "fingerprint": "context-hash"},
        ):
            result = extract_one(export, repo_root=root)

    assert result["artifactId"] == "lean/DAG/Basic.lean"
    assert result["status"] == "partial_structural_candidate_with_recorded_loss"
    assert result["rowCounts"]["raw_infotree_nodes.jsonl"] == 2
    assert result["features"]["node.kind=tactic"] == 1
    assert result["features"]["root.count"] == 1
    assert result["features"]["context.kind=tacticctx"] == 1
    assert result["features"]["payload_field.name=goalsbefore"] == 1
    assert result["features"]["projection_leakage.field=term_expr_graph"] == 1
    serialized_features = json.dumps(result["features"]).lower()
    assert "hiddentheoremname" not in serialized_features
    assert "source text intentionally ignored" not in serialized_features
    assert len(result["dnaFingerprint"]) == 64
    assert len(result["rawCaptureSha256"]) == 64
    assert len(result["rawRowFileSha256"]["raw_infotree_nodes.jsonl"]) == 64


@pytest.mark.parametrize("producer_state", ["missing_receipt", "changed_source", "missing_source"])
def test_audited_extraction_excludes_unknown_or_changed_exporter(tmp_path, producer_state):
    export = tmp_path / "capture/per_file/basic"
    _fixture(tmp_path, export)
    metadata_path = export / "metadata.json"
    exporter = tmp_path / "lean/DAG/RawInfoTreeExport.lean"
    if producer_state == "missing_receipt":
        metadata = json.loads(metadata_path.read_text())
        del metadata["sourceProvenance"]["exporterSourceSha256"]
        metadata_path.write_text(json.dumps(metadata))
    elif producer_state == "changed_source":
        exporter.write_text("-- revised exporter\n")
    else:
        exporter.unlink()
    with patch("tools.repository_evolution.infotree_dna._current_lean_context") as context:
        rows, rejections = extract_tree_audited(tmp_path / "capture", repo_root=tmp_path)
    assert rows == []
    assert len(rejections) == 1
    assert rejections[0]["reason"] == "exporter_source_missing_or_stale"
    context.assert_not_called()


def test_extract_one_preserves_lexical_path_for_in_repo_symlink(tmp_path: Path):
    target = tmp_path / "external/Target.lean"
    target.parent.mkdir(parents=True)
    target.write_text("theorem target : True := True.intro\n", encoding="utf-8")
    alias = tmp_path / "lean/TargetAlias.lean"
    alias.parent.mkdir(parents=True)
    try:
        alias.symlink_to("../external/Target.lean")
    except OSError as exc:
        pytest.skip(f"symlink creation unavailable: {exc}")
    export = tmp_path / "capture/per_file/alias"
    export.mkdir(parents=True)
    source_sha = hashlib.sha256(target.read_bytes()).hexdigest()
    (export / "metadata.json").write_text(json.dumps({
        "schema": "info_geometry.raw_infotree_export.v1",
        "loss_audited": True,
        "fully_lossless": True,
        "leakage_count": 0,
        "sourceProvenance": {
            "sourcePath": "lean/TargetAlias.lean",
            "exporterSourceSha256": _exporter_receipt(tmp_path),
            "sourceSha256": source_sha,
            "leanContextFingerprint": "context-hash",
        },
    }), encoding="utf-8")
    _write_jsonl(export / "raw_infotree_roots.jsonl", [{
        "rootKey": "root-1", "file": "lean/TargetAlias.lean", "module": "TargetAlias",
    }])
    _write_jsonl(export / "raw_infotree_nodes.jsonl", [{"kind": "command"}])
    _write_jsonl(export / "raw_infotree_projection_leakage.jsonl", [])

    with patch(
        "tools.repository_evolution.infotree_dna._current_lean_context",
        return_value={"sourceSha256": source_sha, "fingerprint": "context-hash"},
    ) as context:
        result = extract_one(export, repo_root=tmp_path)

    assert result["artifactId"] == "lean/TargetAlias.lean"
    assert context.call_args.args[1] == alias.absolute()


def test_raw_capture_fingerprint_changes_when_omitted_row_payload_changes():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": hashlib.sha256(
                (root / "lean/DAG/Basic.lean").read_bytes()
            ).hexdigest(), "fingerprint": "context-hash"},
        ):
            before = extract_one(export, repo_root=root)
            _write_jsonl(export / "raw_infotree_payload_fields.jsonl", [{
                "field": "goalsBefore", "value": "different omitted value",
            }])
            after = extract_one(export, repo_root=root)

    assert before["features"] == after["features"]
    assert before["rawCaptureSha256"] != after["rawCaptureSha256"]
    assert before["dnaFingerprint"] != after["dnaFingerprint"]


def test_root_record_is_included_in_dna_and_capture_fingerprint():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        source_sha = hashlib.sha256((root / "lean/DAG/Basic.lean").read_bytes()).hexdigest()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": source_sha, "fingerprint": "context-hash"},
        ):
            before = extract_one(export, repo_root=root)
            _write_jsonl(export / "raw_infotree_roots.jsonl", [{
                "rootKey": "root-1", "file": "lean/DAG/Basic.lean", "module": "renamed.Module",
            }])
            after = extract_one(export, repo_root=root)

    assert before["featureVersion"] == "raw_infotree_structural_dna.v4"
    assert before["features"]["root.count"] == after["features"]["root.count"] == 1
    assert before["rawCaptureSha256"] != after["rawCaptureSha256"]
    assert before["dnaFingerprint"] != after["dnaFingerprint"]


def test_extract_rejects_capture_missing_required_roots_file():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        (export / "raw_infotree_roots.jsonl").unlink()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": hashlib.sha256(
                (root / "lean/DAG/Basic.lean").read_bytes()
            ).hexdigest(), "fingerprint": "context-hash"},
        ):
            with pytest.raises(ValueError, match="required RawInfoTree roots file is missing"):
                extract_one(export, repo_root=root)


def test_extract_rejects_capture_missing_required_leakage_file():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        (export / "raw_infotree_projection_leakage.jsonl").unlink()
        source_sha = hashlib.sha256((root / "lean/DAG/Basic.lean").read_bytes()).hexdigest()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": source_sha, "fingerprint": "context-hash"},
        ):
            with pytest.raises(ValueError, match="required RawInfoTree projection leakage file"):
                extract_one(export, repo_root=root)


def test_extract_rejects_leakage_metadata_count_mismatch():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        metadata_path = export / "metadata.json"
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        metadata["leakage_count"] = 0
        metadata_path.write_text(json.dumps(metadata), encoding="utf-8")
        source_sha = hashlib.sha256((root / "lean/DAG/Basic.lean").read_bytes()).hexdigest()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": source_sha, "fingerprint": "context-hash"},
        ):
            with pytest.raises(ValueError, match="differs from projection leakage row count"):
                extract_one(export, repo_root=root)


def test_projection_leakage_changes_source_dna_fingerprint():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        _fixture(root, export)
        source_sha = hashlib.sha256((root / "lean/DAG/Basic.lean").read_bytes()).hexdigest()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": source_sha, "fingerprint": "context-hash"},
        ):
            before = extract_one(export, repo_root=root)
            _write_jsonl(export / "raw_infotree_projection_leakage.jsonl", [{
                "field": "term_lctx", "reason": "a different omitted structural surface",
            }])
            after = extract_one(export, repo_root=root)

    assert before["features"] != after["features"]
    assert before["rawCaptureSha256"] != after["rawCaptureSha256"]
    assert before["dnaFingerprint"] != after["dnaFingerprint"]


def test_extract_rejects_capture_after_current_source_changes():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        source = _fixture(root, export)
        source.write_text("def sample := 2\n", encoding="utf-8")
        with pytest.raises(ValueError, match="digest does not match"):
            extract_one(export, repo_root=root)


def test_extract_rejects_stale_olean_context_even_when_source_matches():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        export = root / "capture/per_file/basic"
        source = _fixture(root, export)
        current_sha = hashlib.sha256(source.read_bytes()).hexdigest()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": current_sha, "fingerprint": "new-context"},
        ):
            with pytest.raises(ValueError, match="toolchain/olean context differs"):
                extract_one(export, repo_root=root)


def test_extract_tree_rejects_duplicate_current_source_captures():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        _fixture(root, root / "captures/first/per_file/basic")
        _fixture(root, root / "captures/second/per_file/basic")
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": hashlib.sha256(
                (root / "lean/DAG/Basic.lean").read_bytes()
            ).hexdigest(), "fingerprint": "context-hash"},
        ):
            with pytest.raises(ValueError, match="duplicate current-source capture"):
                extract_tree(root / "captures", repo_root=root)


def test_audited_extraction_keeps_valid_dna_and_records_stale_context_separately():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        exports = root / "captures"
        good_dir = exports / "per_file/000_good"
        _fixture(root, good_dir)
        stale_source = root / "lean/DAG/Stale.lean"
        stale_source.write_text("def stale := 1\n", encoding="utf-8")
        stale_dir = exports / "per_file/001_stale"
        stale_dir.mkdir(parents=True)
        stale_sha = hashlib.sha256(stale_source.read_bytes()).hexdigest()
        metadata = json.loads((good_dir / "metadata.json").read_text(encoding="utf-8"))
        metadata["sourceProvenance"]["sourcePath"] = "lean/DAG/Stale.lean"
        metadata["sourceProvenance"]["sourceSha256"] = stale_sha
        (stale_dir / "metadata.json").write_text(json.dumps(metadata), encoding="utf-8")
        _write_jsonl(stale_dir / "raw_infotree_nodes.jsonl", [])
        good_sha = hashlib.sha256((root / "lean/DAG/Basic.lean").read_bytes()).hexdigest()

        def context_for(repo_root: Path, source_path: Path) -> dict[str, str]:
            if source_path.name == "Stale.lean":
                return {"sourceSha256": stale_sha, "fingerprint": "changed-context"}
            return {"sourceSha256": good_sha, "fingerprint": "context-hash"}

        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            side_effect=context_for,
        ):
            records, rejected = extract_tree_audited(exports, repo_root=root)

    assert [record["artifactId"] for record in records] == ["lean/DAG/Basic.lean"]
    assert rejected == [{
        "artifactId": "lean/DAG/Stale.lean",
        "captureDirectory": "per_file/001_stale",
        "reason": "stale_lean_context",
        "errorType": "ValueError",
        "reportedSourceSha256": stale_sha,
        "reportedLeanContextFingerprint": "context-hash",
        "reportedExporterSourceSha256": metadata["sourceProvenance"]["exporterSourceSha256"],
    }]


def test_audited_extraction_reports_invalid_metadata_without_aborting_other_files():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        exports = root / "captures"
        good_dir = exports / "per_file/000_good"
        _fixture(root, good_dir)
        malformed_dir = exports / "per_file/001_malformed"
        malformed_dir.mkdir(parents=True)
        (malformed_dir / "metadata.json").write_text("{not-json", encoding="utf-8")
        good_sha = hashlib.sha256((root / "lean/DAG/Basic.lean").read_bytes()).hexdigest()
        with patch(
            "tools.repository_evolution.infotree_dna._current_lean_context",
            return_value={"sourceSha256": good_sha, "fingerprint": "context-hash"},
        ):
            records, rejected = extract_tree_audited(exports, repo_root=root)

    assert len(records) == 1
    assert rejected == [{
        "artifactId": None,
        "captureDirectory": "per_file/001_malformed",
        "reason": "invalid_capture",
        "errorType": "JSONDecodeError",
        "reportedSourceSha256": None,
        "reportedLeanContextFingerprint": None,
        "reportedExporterSourceSha256": None,
    }]


def test_compute_multiscale_dna_affinity_clusters_groups_homologous_records():
    rec_a1 = {
        "artifactId": "lean/InfoGeometry/Canonical/HomologA1.lean",
        "features": [
            {"kind": "tacticName", "value": "simp", "count": 12},
            {"kind": "path2", "value": "command->tactic->term", "count": 20},
            {"kind": "goalShape", "value": "⊢_=_", "count": 15},
        ],
        "structuralSummary": {"totalNodes": 40, "maxDepth": 6, "branchingNodes": 8, "tacticSteps": 12},
    }
    rec_a2 = {
        "artifactId": "lean/InfoGeometry/Canonical/HomologA2.lean",
        "features": [
            {"kind": "tacticName", "value": "simp", "count": 11},
            {"kind": "path2", "value": "command->tactic->term", "count": 19},
            {"kind": "goalShape", "value": "⊢_=_", "count": 16},
        ],
        "structuralSummary": {"totalNodes": 42, "maxDepth": 6, "branchingNodes": 8, "tacticSteps": 11},
    }
    rec_b1 = {
        "artifactId": "lean/InfoGeometry/Canonical/DistinctB1.lean",
        "features": [
            {"kind": "tacticName", "value": "induction", "count": 10},
            {"kind": "path2", "value": "command->context->completion", "count": 18},
            {"kind": "goalShape", "value": "⊢∀_,_", "count": 14},
        ],
        "structuralSummary": {"totalNodes": 90, "maxDepth": 16, "branchingNodes": 30, "tacticSteps": 10},
    }

    report = compute_multiscale_dna_affinity_clusters([rec_a1, rec_a2, rec_b1], betas=(0.5, 4.0))
    assert report["schema"] == "info_geometry.infotree_dna_multiscale_archetypes.v1"
    assert report["recordCount"] == 3
    assert len(report["scales"]) == 2
    high_beta = report["scales"][-1]
    member_sets = [set(c["members"]) for c in high_beta["clusters"]]
    assert {
        "lean/InfoGeometry/Canonical/HomologA1.lean",
        "lean/InfoGeometry/Canonical/HomologA2.lean",
    } in member_sets
