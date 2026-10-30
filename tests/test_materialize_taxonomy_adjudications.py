from __future__ import annotations

import copy

import pytest

from tools.repository_evolution.materialize_taxonomy_adjudications import (
    ANNOTATION_SCHEMA,
    DECISION_SCHEMA,
    materialize_adjudications,
)
from tools.repository_evolution.reviewed_taxonomy_corpus import build_reviewed_corpus
from tools.repository_evolution.taxonomy_adjudication_queue import build_adjudication_queue
from tests.test_taxonomy_adjudication_queue import _fixture


def _queue(tmp_path):
    report = _fixture(tmp_path)
    report["sourceSnapshot"]["pathContentManifestSha256"] = "a" * 64
    tasks, manifest = build_adjudication_queue(report, tmp_path, limit=4, seed="review-round")
    return report, tasks, manifest


def test_human_decisions_materialize_as_reviewed_corpus_annotations(tmp_path):
    report, tasks, manifest = _queue(tmp_path)
    selected = [task for task in tasks if task["artifactId"] == "lean/A.lean"]
    decisions = [{
        "schema": DECISION_SCHEMA,
        "taskId": task["taskId"],
        "decision": "label",
        "reviewerId": reviewer,
        "labels": (["formal_source"] if task["facet"] == "artifact_role"
                   else ["proof_development"]),
        "labelDefinitions": ({"formal_source": "A Lean source artifact with formal declarations"}
                             if task["facet"] == "artifact_role" else
                             {"proof_development": "A module developing formal proofs"}),
        "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1}],
    } for task in selected for reviewer in ("reviewer-1", "reviewer-2")]
    annotations, materialization = materialize_adjudications(
        tasks, manifest, decisions, tmp_path,
    )
    assert len(annotations) == 2
    assert all(row["schema"] == ANNOTATION_SCHEMA for row in annotations)
    assert all(row["reviewStatus"] == "human_adjudicated" for row in annotations)
    assert all(row["reviewerIds"] == ["reviewer-1", "reviewer-2"] for row in annotations)
    assert all(row["consensusMethod"] == "unanimous_exact_label_set" for row in annotations)
    assert all(row["evidence"][0]["sourceSha256"] == row["sourceSha256"]
               for row in annotations)
    assert materialization["unansweredTaskCount"] == len(tasks) - 2
    assert materialization["interRaterAgreementByFacet"]["artifact_role"][
        "exactSetAgreementRate"] == 1.0

    corpus = build_reviewed_corpus(report, annotations, tmp_path)
    corpus_row = next(row for row in corpus["rows"] if row["artifactId"] == "lean/A.lean")
    assert corpus_row["labels"]["artifact_role"] == ["formal_source"]
    assert corpus_row["labels"]["semantic_archetype"] == ["proof_development"]


def test_converter_rejects_tampered_queue_rows_and_duplicate_decisions(tmp_path):
    _, tasks, manifest = _queue(tmp_path)
    tampered = copy.deepcopy(tasks)
    tampered[0]["labels"] = ["unreviewed"]
    with pytest.raises(ValueError, match="task digest differs"):
        materialize_adjudications(tampered, manifest, [], tmp_path)

    task = tasks[0]
    decision = {"schema": DECISION_SCHEMA, "taskId": task["taskId"],
                "reviewerId": "reviewer-1", "decision": "pending"}
    with pytest.raises(ValueError, match="duplicate decision from reviewer"):
        materialize_adjudications(tasks, manifest, [decision, decision], tmp_path)


def test_converter_checks_reviewed_source_digest_and_span_bounds(tmp_path):
    _, tasks, manifest = _queue(tmp_path)
    task = next(task for task in tasks if task["artifactId"] == "lean/A.lean")
    decision = [{
        "schema": DECISION_SCHEMA, "taskId": task["taskId"], "decision": "label",
        "reviewerId": reviewer, "labels": ["formal_source"],
        "labelDefinitions": {"formal_source": "A Lean source artifact with formal declarations"},
        "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 2}],
    } for reviewer in ("reviewer-1", "reviewer-2")]
    with pytest.raises(ValueError, match="invalid source span"):
        materialize_adjudications(tasks, manifest, decision, tmp_path)
    (tmp_path / task["artifactId"]).write_text("changed after queue\n", encoding="utf-8")
    valid_spans = copy.deepcopy(decision)
    for vote in valid_spans:
        vote["evidence"][0]["endLine"] = 1
    with pytest.raises(ValueError, match="source hash differs"):
        materialize_adjudications(tasks, manifest, valid_spans, tmp_path)


def test_disagreement_is_reported_and_never_materialized_as_a_training_label(tmp_path):
    _, tasks, manifest = _queue(tmp_path)
    task = next(task for task in tasks if task["facet"] == "artifact_role")
    votes = [{
        "schema": DECISION_SCHEMA, "taskId": task["taskId"], "decision": "label",
        "reviewerId": reviewer, "labels": [label],
        "labelDefinitions": {label: f"A reviewed {label.replace('_', ' ')} artifact"},
        "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1}],
    } for reviewer, label in (("reviewer-1", "formal_source"),
                              ("reviewer-2", "repository_source"))]

    annotations, report = materialize_adjudications(tasks, manifest, votes, tmp_path)

    assert annotations == []
    assert report["disagreementTaskCount"] == 1
    assert report["disagreementTaskIds"] == [task["taskId"]]
    assert report["interRaterAgreementByFacet"]["artifact_role"][
        "exactSetAgreementRate"] == 0.0


def test_one_reviewer_is_not_enough_to_promote_a_label(tmp_path):
    _, tasks, manifest = _queue(tmp_path)
    task = next(task for task in tasks if task["facet"] == "artifact_role")
    vote = {
        "schema": DECISION_SCHEMA, "taskId": task["taskId"], "decision": "label",
        "reviewerId": "reviewer-1", "labels": ["formal_source"],
        "labelDefinitions": {"formal_source": "A Lean source artifact with formal declarations"},
        "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1}],
    }

    annotations, report = materialize_adjudications(tasks, manifest, [vote], tmp_path)

    assert annotations == []
    assert report["insufficientIndependentReviewersTaskCount"] == 1
    assert report["interRaterAgreementByFacet"]["artifact_role"][
        "exactSetAgreementRate"] is None


def test_definition_disagreement_blocks_consensus_even_when_label_set_matches(tmp_path):
    _, tasks, manifest = _queue(tmp_path)
    task = next(task for task in tasks if task["facet"] == "artifact_role")
    votes = [{
        "schema": DECISION_SCHEMA, "taskId": task["taskId"], "decision": "label",
        "reviewerId": "reviewer-1", "labels": ["formal_source"],
        "labelDefinitions": {"formal_source": "A formal Lean source artifact"},
        "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1}],
    }, {
        "schema": DECISION_SCHEMA, "taskId": task["taskId"], "decision": "label",
        "reviewerId": "reviewer-2", "labels": ["formal_source"],
        "labelDefinitions": {"formal_source": "A repository source file with declarations"},
        "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1}],
    }]

    annotations, report = materialize_adjudications(tasks, manifest, votes, tmp_path)

    assert annotations == []
    assert report["disagreementTaskCount"] == 1
    assert report["interRaterAgreementByFacet"]["artifact_role"][
        "definitionAgreementRate"] == 0.0


def test_unanimous_empty_label_set_is_a_valid_complete_multilabel_annotation(tmp_path):
    report, tasks, manifest = _queue(tmp_path)
    task = next(task for task in tasks if task["facet"] == "semantic_archetype")
    votes = [{
        "schema": DECISION_SCHEMA, "taskId": task["taskId"], "decision": "label",
        "reviewerId": reviewer, "labels": [], "labelDefinitions": {}, "labelSetComplete": True,
        "evidence": [{"kind": "source_span", "startLine": 1, "endLine": 1}],
    } for reviewer in ("reviewer-1", "reviewer-2")]

    annotations, summary = materialize_adjudications(tasks, manifest, votes, tmp_path)
    corpus = build_reviewed_corpus(report, annotations, tmp_path)
    row = next(row for row in corpus["rows"] if row["artifactId"] == task["artifactId"])

    assert annotations[0]["labels"] == []
    assert summary["interRaterAgreementByFacet"]["semantic_archetype"]["meanJaccard"] == 1.0
    assert row["labels"]["semantic_archetype"] == []
    assert row["labelSetCompleteByFacet"]["semantic_archetype"] is True
