from __future__ import annotations

import copy
import hashlib
from collections import Counter
from pathlib import Path

import pytest

from tools.repository_evolution.reviewed_taxonomy_corpus import (
    ANNOTATION_SCHEMA,
    _iterative_group_splits,
    _split_group,
    build_reviewed_corpus,
)


def _fixture(tmp_path: Path):
    root = tmp_path / "repo"
    root.mkdir()
    contents = {
        "lean/Alpha.lean": "theorem alpha : True := True.intro\n",
        "lean/Beta.lean": "theorem beta : True := True.intro\n",
        "lean/Gamma.lean": "theorem gamma : True := True.intro\n",
        "lean/Delta.lean": "theorem delta : True := True.intro\n",
    }
    files = []
    annotations = []
    for index, (artifact, source) in enumerate(contents.items()):
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        sha = hashlib.sha256(source.encode()).hexdigest()
        module = f"Lean.Module{index}" if index != 1 else "Lean.Module0"
        files.append({"path": artifact, "contentSha256": sha, "module": module,
                      "owner": "Root", "role": "lean_source", "lineCount": 1})
        annotations.append({
            "schema": ANNOTATION_SCHEMA,
            "annotationId": f"annotation-{index}",
            "artifactId": artifact,
            "sourceSnapshotSha256": "a" * 64,
            "sourceSha256": sha,
            "facet": "artifact_role",
            "labels": ["formal_source"],
            "labelDefinitions": {"formal_source": "A Lean source artifact with formal declarations"},
            "reviewStatus": "human_adjudicated",
            "labelSetComplete": True,
            "reviewerId": "reviewer-1",
            "reviewerIds": ["reviewer-1", "reviewer-2"],
            "independentReviewerCount": 2,
            "consensusMethod": "unanimous_exact_label_set",
            "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1,
                          "sourceSha256": sha, "reviewerId": reviewer}
                         for reviewer in ("reviewer-1", "reviewer-2")],
        })
    report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {"worktreeConsistentDuringScan": True,
                           "pathContentManifestSha256": "a" * 64},
        "analysisProvenance": {"analysisInputsConsistentDuringScan": True,
                               "scannerSourceSha256": "b" * 64,
                               "lakeManifestSha256": "c" * 64},
        "files": files,
        "dependencyEdges": [{"from": "lean/Alpha.lean", "to": "lean/Gamma.lean",
                             "kind": "lean_source_import"}],
        "leanDeclarationCandidates": [{"sourcePath": "lean/Alpha.lean", "kind": "theorem"}],
    }
    return root, report, annotations


def test_corpus_binds_reviewed_labels_to_current_source_and_group_splits(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    result = build_reviewed_corpus(report, annotations, root, split_seed="test")
    assert result["schema"] == "info_geometry.reviewed_taxonomy_corpus_manifest.v4"
    assert result["corpusSchema"] == "info_geometry.reviewed_taxonomy_corpus.v4"
    rows = {row["artifactId"]: row for row in result["rows"]}
    assert rows["lean/Alpha.lean"]["splitGroup"] == rows["lean/Beta.lean"]["splitGroup"]
    assert rows["lean/Alpha.lean"]["split"] == rows["lean/Beta.lean"]["split"]
    assert rows["lean/Alpha.lean"]["labels"] == {"artifact_role": ["formal_source"]}
    assert rows["lean/Alpha.lean"]["labelDefinitionsByFacet"] == {
        "artifact_role": {"formal_source": "A Lean source artifact with formal declarations"}
    }
    assert result["labelCodebook"] == [{
        "facet": "artifact_role", "label": "formal_source",
        "definition": "A Lean source artifact with formal declarations",
    }]
    assert rows["lean/Alpha.lean"]["labelSetCompleteByFacet"] == {"artifact_role": True}
    assert rows["lean/Alpha.lean"]["consensusByFacet"]["artifact_role"] == {
        "reviewerIds": ["reviewer-1", "reviewer-2"],
        "independentReviewerCount": 2,
        "method": "unanimous_exact_label_set",
    }
    assert rows["lean/Alpha.lean"]["modelInput"]["sourceText"].startswith("theorem alpha")
    assert rows["lean/Alpha.lean"]["modelInput"]["typedNeighborhoodCounts"] == {
        "outgoing:lean_source_import": 1
    }
    assert rows["lean/Alpha.lean"]["modelInput"]["declarationKindCounts"] == {"theorem": 1}
    assert result["annotationCount"] == 4
    assert result["corpusRowsSha256"]
    assert result["splitStrategy"] == "iterative_multilabel_module_owner_content_group_holdout_v3"
    assert sum(result["splitLabelCounts"][split].get("artifact_role=formal_source", 0)
               for split in ("train", "validation", "test")) == 4


def test_corpus_rejects_conflicting_definitions_for_same_facet_label(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[1]["labelDefinitions"]["formal_source"] = "A different source role definition"
    with pytest.raises(ValueError, match="conflicting definitions"):
        build_reviewed_corpus(report, annotations, root)


def test_corpus_rejects_evidence_witness_bound_to_another_source(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[0]["evidence"][0]["sourceSha256"] = "0" * 64
    with pytest.raises(ValueError, match="witness hash differs"):
        build_reviewed_corpus(report, annotations, root)


def test_split_groups_unindexed_module_candidates_without_pseudo_owner_leakage():
    first = {
        "path": "lean/audit/AuditNative.lean",
        "moduleCandidate": "AuditNative",
        "moduleCandidateSourceRoot": "lean",
        "moduleCandidateStatus": "lexical_source_root_candidate_not_lake_indexed",
        "owner": "unresolved_lean_module",
        "ownerStatus": "uncertain_module_not_in_lake_target_index",
    }
    same_module = {
        **first,
        "path": "lean/other/AuditNative.lean",
    }
    other_source_root = {
        **first,
        "path": "support/AuditNative.lean",
        "moduleCandidateSourceRoot": "support",
    }
    assert _split_group(first) == _split_group(same_module)
    assert _split_group(first) != _split_group(other_source_root)
    assert _split_group(first) != "owner:unresolved_lean_module"


def test_iterative_multilabel_split_balances_rare_labels_without_splitting_groups():
    group_labels = {
        f"module:{index}": Counter({
            "artifact_role=lean_source": 1,
            **({"semantic_archetype=rare_operator_bridge": 1} if index < 4 else {}),
        })
        for index in range(20)
    }
    group_sizes = {group: 1 for group in group_labels}

    splits = _iterative_group_splits(group_labels, group_sizes, seed="iterative-test")
    repeated = _iterative_group_splits(group_labels, group_sizes, seed="iterative-test")

    assert splits == repeated
    assert set(splits) == set(group_labels)
    rare_label_splits = {
        splits[group] for group, labels in group_labels.items()
        if "semantic_archetype=rare_operator_bridge" in labels
    }
    assert rare_label_splits == {"train", "validation", "test"}


def test_corpus_rejects_weak_or_non_adjudicated_labels(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[0]["reviewStatus"] = "weak_rule"
    with pytest.raises(ValueError, match="human_adjudicated"):
        build_reviewed_corpus(report, annotations, root)


def test_corpus_rejects_single_reviewer_labels_even_if_marked_adjudicated(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[0].pop("reviewerIds")
    annotations[0].pop("independentReviewerCount")
    annotations[0].pop("consensusMethod")

    with pytest.raises(ValueError, match="at least two distinct consensus reviewerIds"):
        build_reviewed_corpus(report, annotations, root)


def test_corpus_rejects_wrong_snapshot_or_source_hash(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[0]["sourceSnapshotSha256"] = "d" * 64
    with pytest.raises(ValueError, match="snapshot differs"):
        build_reviewed_corpus(report, annotations, root)
    annotations[0]["sourceSnapshotSha256"] = "a" * 64
    annotations[0]["sourceSha256"] = "e" * 64
    with pytest.raises(ValueError, match="source hash differs"):
        build_reviewed_corpus(report, annotations, root)


def test_corpus_rejects_stale_span_and_current_file_edits(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[0]["evidence"][0]["endLine"] = 2
    with pytest.raises(ValueError, match="exceeds current file length"):
        build_reviewed_corpus(report, annotations, root)
    annotations[0]["evidence"][0]["endLine"] = 1
    (root / "lean/Alpha.lean").write_text("theorem edited : True := True.intro\n", encoding="utf-8")
    with pytest.raises(ValueError, match="changed or is unavailable"):
        build_reviewed_corpus(report, annotations, root)


def test_corpus_refuses_map_without_consistent_analyzer_provenance(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    report["analysisProvenance"]["analysisInputsConsistentDuringScan"] = False
    with pytest.raises(ValueError, match="missing or unstable"):
        build_reviewed_corpus(report, annotations, root)


def test_corpus_rejects_annotations_that_do_not_close_the_facet_label_set(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    annotations[0]["labelSetComplete"] = False
    with pytest.raises(ValueError, match="labelSetComplete=true"):
        build_reviewed_corpus(report, annotations, root)


def test_exact_content_clones_share_the_same_group_holdout_across_modules(tmp_path: Path):
    root, report, annotations = _fixture(tmp_path)
    clone_artifact = "lean/Clone.lean"
    clone_source = (root / "lean/Alpha.lean").read_text(encoding="utf-8")
    (root / clone_artifact).write_text(clone_source, encoding="utf-8")
    clone_sha = hashlib.sha256(clone_source.encode()).hexdigest()
    report["files"].append({
        "path": clone_artifact, "contentSha256": clone_sha,
        "module": "Lean.Unrelated.Clone", "owner": "UnrelatedRoot",
        "role": "lean_source", "lineCount": 1,
    })
    clone_annotation = copy.deepcopy(annotations[0])
    clone_annotation.update({
        "annotationId": "annotation-clone", "artifactId": clone_artifact,
        "sourceSha256": clone_sha,
    })
    clone_annotation["evidence"][0]["sourceSha256"] = clone_sha
    result = build_reviewed_corpus(report, [*annotations, clone_annotation], root,
                                   split_seed="clone-test")
    rows = {row["artifactId"]: row for row in result["rows"]}
    assert rows["lean/Alpha.lean"]["sourceSha256"] == rows[clone_artifact]["sourceSha256"]
    assert rows["lean/Alpha.lean"]["splitGroup"] == rows[clone_artifact]["splitGroup"]
    assert rows["lean/Alpha.lean"]["split"] == rows[clone_artifact]["split"]
