from __future__ import annotations

import copy
import hashlib
import json

import pytest

from tools.repository_evolution.taxonomy_training_readiness import (
    audit_training_readiness,
)


def _corpus():
    assignments = [
        ("train", "formal"), ("train", "formal"), ("train", "tooling"),
        ("train", "tooling"), ("validation", "formal"), ("validation", "tooling"),
        ("test", "formal"), ("test", "tooling"),
    ]
    rows = [{
        "artifactId": f"artifact-{index}.lean",
        "sourceSha256": hashlib.sha256(f"artifact-{index}.lean".encode()).hexdigest(),
        "splitGroup": f"module:{index}",
        "split": split,
        "labels": {"artifact_role": [label]},
        "labelDefinitionsByFacet": {"artifact_role": {
            label: f"A reviewed {label} codebase artifact"
        }},
        "labelSetCompleteByFacet": {"artifact_role": True},
        "consensusByFacet": {"artifact_role": {
            "reviewerIds": ["reviewer-1", "reviewer-2"],
            "independentReviewerCount": 2,
            "method": "unanimous_exact_label_set",
        }},
    } for index, (split, label) in enumerate(assignments)]
    encoded = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
        for row in rows
    )
    corpus = {
        "schema": "info_geometry.reviewed_taxonomy_corpus_manifest.v4",
        "corpusSchema": "info_geometry.reviewed_taxonomy_corpus.v4",
        "artifactCount": len(rows),
        "splitCounts": {"train": 4, "validation": 2, "test": 2},
        "corpusRowsSha256": hashlib.sha256(encoded).hexdigest(),
        "labelCodebookSchema": "info_geometry.taxonomy_label_codebook.v1",
        "labelCodebook": [
            {"facet": "artifact_role", "label": label,
             "definition": f"A reviewed {label} codebase artifact"}
            for label in ("formal", "tooling")
        ],
        "rows": rows,
    }
    payload = {"schema": "info_geometry.taxonomy_label_codebook.v1",
               "labels": corpus["labelCodebook"]}
    corpus["labelCodebookSha256"] = hashlib.sha256(
        json.dumps(payload, sort_keys=True, ensure_ascii=False,
                   separators=(",", ":")).encode()
    ).hexdigest()
    return corpus


def test_readiness_requires_represented_labels_in_all_splits():
    report = audit_training_readiness(_corpus())
    assert report["readyForSupervisedTraining"] is True
    assert report["blockers"] == []
    assert report["labelCoverageByFacet"]["artifact_role"]["formal"] == {
        "train": 2, "validation": 1, "test": 1
    }
    assert report["labelGroupCoverageByFacet"]["artifact_role"]["formal"] == {
        "train": {"positiveGroups": 2, "negativeGroups": 2},
        "validation": {"positiveGroups": 1, "negativeGroups": 1},
        "test": {"positiveGroups": 1, "negativeGroups": 1},
    }
    assert report["labelsMissingNegativeTrainingExamples"] == []
    assert report["labelsMissingNegativeEvaluationExamples"] == []


@pytest.mark.parametrize("labels", [
    [["formal"]], [{"label": "formal"}], [None], [7],
    ["formal", "formal"], [" formal"], "formal",
])
def test_malformed_labels_produce_blockers_without_crashing_or_counting(labels):
    corpus = _corpus()
    corpus["rows"][0]["labels"]["artifact_role"] = labels
    corpus["corpusRowsSha256"] = hashlib.sha256(b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
        for row in corpus["rows"]
    )).hexdigest()
    report = audit_training_readiness(corpus)
    assert report["readyForSupervisedTraining"] is False
    assert "malformed_rows" in report["blockers"]
    assert report["malformedRowIndices"] == [0]
    assert report["labelCoverageByFacet"]["artifact_role"]["formal"]["train"] == 1


def test_readiness_blocks_split_groups_leaking():
    corpus = _corpus()
    corpus["rows"][-2]["splitGroup"] = corpus["rows"][4]["splitGroup"]
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
                 for row in corpus["rows"])
    ).hexdigest()
    report = audit_training_readiness(corpus)
    assert report["readyForSupervisedTraining"] is False
    assert "split_group_leakage" in report["blockers"]


def test_readiness_counts_independent_groups_not_only_rows():
    corpus = _corpus()
    corpus["rows"][1]["splitGroup"] = corpus["rows"][0]["splitGroup"]
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
                 for row in corpus["rows"])
    ).hexdigest()

    report = audit_training_readiness(corpus)

    assert report["labelCoverageByFacet"]["artifact_role"]["formal"]["train"] == 2
    assert report["labelGroupCoverageByFacet"]["artifact_role"]["formal"]["train"] == {
        "positiveGroups": 1, "negativeGroups": 2,
    }
    assert "labels_below_minimum_independent_training_groups" in report["blockers"]


def test_readiness_blocks_label_codebook_digest_tampering():
    corpus = _corpus()
    corpus["labelCodebook"][0]["definition"] = "A tampered label meaning"
    report = audit_training_readiness(corpus)
    assert "label_codebook_digest_or_catalog_mismatch" in report["blockers"]


def test_readiness_detects_manifest_or_row_digest_tampering():
    corpus = _corpus()
    corpus["rows"][0]["labels"]["artifact_role"] = ["changed"]
    report = audit_training_readiness(corpus)
    assert "corpus_rows_digest_mismatch" in report["blockers"]
    assert report["corpusRowsSha256Verified"] is False


def test_readiness_blocks_open_world_labels_for_binary_training():
    corpus = _corpus()
    corpus["rows"][0]["labelSetCompleteByFacet"]["artifact_role"] = False
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
                 for row in corpus["rows"])
    ).hexdigest()
    report = audit_training_readiness(corpus)
    assert "incomplete_label_set_semantics" in report["blockers"]


def test_readiness_requires_independent_reviewer_consensus_receipts():
    corpus = _corpus()
    corpus["rows"][0].pop("consensusByFacet")
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
                 for row in corpus["rows"])
    ).hexdigest()

    report = audit_training_readiness(corpus)

    assert "insufficient_independent_review_consensus" in report["blockers"]


def test_readiness_requires_negative_examples_in_each_evaluation_split():
    corpus = _corpus()
    corpus["rows"][5]["labels"]["artifact_role"] = ["formal"]
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
                 for row in corpus["rows"])
    ).hexdigest()
    report = audit_training_readiness(corpus)
    assert "labels_missing_negative_evaluation_examples" in report["blockers"]


def test_complete_empty_label_sets_count_as_negative_examples():
    corpus = _corpus()
    for row in corpus["rows"]:
        row["labels"]["semantic_archetype"] = []
        row["labelDefinitionsByFacet"]["semantic_archetype"] = {}
        row["labelSetCompleteByFacet"]["semantic_archetype"] = True
        row["consensusByFacet"]["semantic_archetype"] = {
            "reviewerIds": ["reviewer-1", "reviewer-2"],
            "independentReviewerCount": 2,
            "method": "unanimous_exact_label_set",
        }
    for split in ("train", "validation", "test"):
        positives = [row for row in corpus["rows"] if row["split"] == split]
        positive_count = 2 if split == "train" else 1
        for row in positives[:positive_count]:
            row["labels"]["semantic_archetype"] = ["operator_bridge"]
            row["labelDefinitionsByFacet"]["semantic_archetype"] = {
                "operator_bridge": "A reviewed operator bridge archetype"
            }
    corpus["labelCodebook"].append({
        "facet": "semantic_archetype", "label": "operator_bridge",
        "definition": "A reviewed operator bridge archetype",
    })
    codebook_payload = {"schema": "info_geometry.taxonomy_label_codebook.v1",
                        "labels": corpus["labelCodebook"]}
    corpus["labelCodebookSha256"] = hashlib.sha256(json.dumps(
        codebook_payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()).hexdigest()
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
                 for row in corpus["rows"])
    ).hexdigest()

    report = audit_training_readiness(corpus)

    assert report["readyForSupervisedTraining"] is True
    assert report["labelCoverageByFacet"]["semantic_archetype"]["operator_bridge"] == {
        "train": 2, "validation": 1, "test": 1,
    }
    assert report["labelsMissingNegativeTrainingExamples"] == []
    assert report["labelsMissingNegativeEvaluationExamples"] == []


def test_readiness_blocks_identical_source_bytes_crossing_splits():
    corpus = _corpus()
    corpus["rows"][6]["sourceSha256"] = corpus["rows"][0]["sourceSha256"]
    corpus["corpusRowsSha256"] = hashlib.sha256(
        b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
                 for row in corpus["rows"])
    ).hexdigest()
    report = audit_training_readiness(corpus)
    assert "duplicate_source_hash_split_leakage" in report["blockers"]


def test_readiness_rejects_invalid_minimum_and_schema():
    with pytest.raises(ValueError, match="positive integer"):
        audit_training_readiness(_corpus(), minimum_train_examples_per_label=0)
    malformed = copy.deepcopy(_corpus())
    malformed["schema"] = "unknown"
    with pytest.raises(ValueError, match="expected schema"):
        audit_training_readiness(malformed)
