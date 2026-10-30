#!/usr/bin/env python3
"""Validate human decisions and materialize reviewed taxonomy annotations.

This is the trust boundary between queue tasks and supervised labels. It never
creates labels: each emitted annotation must come from an explicit human
decision with complete facet scope and source-span evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Any

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))


TASK_SCHEMA = "info_geometry.taxonomy_adjudication_task.v2"
QUEUE_MANIFEST_SCHEMA = "info_geometry.taxonomy_adjudication_queue_manifest.v2"
DECISION_SCHEMA = "info_geometry.taxonomy_review_decision.v2"
ANNOTATION_SCHEMA = "info_geometry.reviewed_taxonomy_annotation.v4"
FACETS = {"artifact_role", "semantic_archetype"}


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _is_sha256(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    try:
        int(value, 16)
    except ValueError:
        return False
    return True


def _rows_digest(rows: list[dict[str, Any]]) -> str:
    payload = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
        for row in rows
    )
    return _sha256(payload)


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected an object")
            rows.append(row)
    return rows


def _validate_queue(tasks: list[dict[str, Any]], manifest: dict[str, Any]
                    ) -> dict[str, dict[str, Any]]:
    if manifest.get("schema") != QUEUE_MANIFEST_SCHEMA:
        raise ValueError(f"expected queue manifest schema {QUEUE_MANIFEST_SCHEMA}")
    if manifest.get("taskCount") != len(tasks):
        raise ValueError("queue manifest task count does not match task rows")
    if manifest.get("taskRowsSha256") != _rows_digest(tasks):
        raise ValueError("queue task digest differs from the manifest")
    snapshot = manifest.get("sourceSnapshotSha256")
    if not _is_sha256(snapshot):
        raise ValueError("queue manifest has no source snapshot SHA-256")
    by_id: dict[str, dict[str, Any]] = {}
    for task in tasks:
        task_id = task.get("taskId")
        artifact, facet = task.get("artifactId"), task.get("facet")
        if task.get("schema") != TASK_SCHEMA or not isinstance(task_id, str):
            raise ValueError("queue contains a malformed task row")
        if not isinstance(artifact, str) or facet not in FACETS:
            raise ValueError(f"queue task {task_id} has an unsupported artifact/facet")
        expected_id = _sha256(f"{snapshot}\0{artifact}\0{facet}".encode("utf-8"))
        if task_id != expected_id:
            raise ValueError(f"queue task identity is invalid for {artifact}/{facet}")
        if task.get("sourceSnapshotSha256") != snapshot:
            raise ValueError(f"queue task snapshot differs for {artifact}")
        if not _is_sha256(task.get("sourceSha256")):
            raise ValueError(f"queue task has no source SHA-256: {artifact}")
        if task.get("reviewStatus") != "pending_human_adjudication":
            raise ValueError(f"queue task is not an unreviewed prompt: {task_id}")
        if task.get("labels") != [] or task.get("labelSetComplete") is not None:
            raise ValueError(f"queue task contains preassigned labels: {task_id}")
        if task_id in by_id:
            raise ValueError(f"duplicate task id: {task_id}")
        by_id[task_id] = task
    return by_id


def materialize_adjudications(tasks: list[dict[str, Any]], manifest: dict[str, Any],
                              decisions: list[dict[str, Any]], repo_root: Path, *,
                              minimum_independent_reviewers: int = 2,
                              ) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Materialize unanimous, independently reviewed decisions as annotations."""
    if (isinstance(minimum_independent_reviewers, bool)
            or not isinstance(minimum_independent_reviewers, int)
            or minimum_independent_reviewers < 2):
        raise ValueError("minimum_independent_reviewers must be at least two")
    task_by_id = _validate_queue(tasks, manifest)
    root = repo_root.resolve()
    seen: set[tuple[str, str]] = set()
    decisions_by_task: dict[str, list[dict[str, Any]]] = defaultdict(list)
    source_cache: dict[str, tuple[str, int]] = {}
    for decision in decisions:
        task_id = decision.get("taskId")
        if decision.get("schema") != DECISION_SCHEMA:
            raise ValueError("decision row has an unsupported schema")
        if not isinstance(task_id, str) or task_id not in task_by_id:
            raise ValueError(f"decision references an unknown task: {task_id!r}")
        reviewer = decision.get("reviewerId")
        if not isinstance(reviewer, str) or not reviewer.strip():
            raise ValueError(f"decision for {task_id} requires reviewerId")
        reviewer = reviewer.strip()
        identity = (task_id, reviewer)
        if identity in seen:
            raise ValueError(f"duplicate decision from reviewer {reviewer} for task {task_id}")
        seen.add(identity)
        normalized_decision = dict(decision)
        normalized_decision["reviewerId"] = reviewer
        status = decision.get("decision")
        if status not in {"label", "skip", "pending"}:
            raise ValueError(f"decision {task_id} must be label, skip, or pending")
        if status == "label":
            labels = decision.get("labels")
            if (not isinstance(labels, list)
                    or any(not isinstance(label, str) or not label.strip()
                           or label != label.strip() for label in labels)
                    or len(labels) != len(set(labels))):
                raise ValueError(f"decision {task_id} requires a complete set of unique non-empty label strings")
            label_definitions = decision.get("labelDefinitions")
            if (not isinstance(label_definitions, dict)
                    or set(label_definitions) != set(labels)
                    or any(not isinstance(value, str) or len(value.split()) < 2
                           or value != " ".join(value.split())
                           for value in label_definitions.values())):
                raise ValueError(
                    f"decision {task_id} requires one normalized definition per selected label"
                )
            if decision.get("labelSetComplete") is not True:
                raise ValueError(f"decision {task_id} must confirm labelSetComplete=true")
            evidence = decision.get("evidence")
            if not isinstance(evidence, list) or not evidence:
                raise ValueError(f"decision {task_id} requires source-span evidence")
            task = task_by_id[task_id]
            artifact = task["artifactId"]
            if artifact not in source_cache:
                source_path = (root / artifact).resolve()
                try:
                    source_path.relative_to(root)
                except ValueError as exc:
                    raise ValueError(f"task source path escapes repository: {artifact}") from exc
                if not source_path.is_file():
                    raise ValueError(f"reviewed source is missing: {artifact}")
                raw = source_path.read_bytes()
                source_sha = _sha256(raw)
                if source_sha != task.get("sourceSha256"):
                    raise ValueError(f"reviewed source hash differs from queue task: {artifact}")
                try:
                    line_count = len(raw.decode("utf-8").splitlines())
                except UnicodeDecodeError as exc:
                    raise ValueError(f"reviewed source is not UTF-8 text: {artifact}") from exc
                source_cache[artifact] = (source_sha, line_count)
            source_sha, source_line_count = source_cache[artifact]
            for witness in evidence:
                if not isinstance(witness, dict) or witness.get("kind") != "source_span":
                    raise ValueError(f"decision {task_id} evidence must use source_span")
                start, end = witness.get("startLine"), witness.get("endLine")
                if (isinstance(start, bool) or isinstance(end, bool)
                        or not isinstance(start, int) or not isinstance(end, int)
                        or start < 1 or end < start or end > source_line_count):
                    raise ValueError(f"decision {task_id} has an invalid source span")
            normalized_decision["labels"] = sorted(labels)
            normalized_decision["labelDefinitions"] = {
                label: label_definitions[label] for label in sorted(labels)
            }
        decisions_by_task[task_id].append(normalized_decision)

    annotations = []
    skipped = pending = insufficient = disagreement = 0
    exact_agreement_pairs: dict[str, int] = Counter()
    comparable_pairs: dict[str, int] = Counter()
    jaccard_sums: dict[str, float] = Counter()
    definition_agreement_pairs: dict[str, int] = Counter()
    definition_comparable_pairs: dict[str, int] = Counter()
    disagreement_task_ids = []
    annotations_per_facet: Counter[str] = Counter()
    for task_id, task in task_by_id.items():
        task_decisions = decisions_by_task.get(task_id, [])
        if not task_decisions:
            continue
        facet = task["facet"]
        label_votes = [row for row in task_decisions if row["decision"] == "label"]
        for left, right in combinations(label_votes, 2):
            comparable_pairs[facet] += 1
            left_labels, right_labels = set(left["labels"]), set(right["labels"])
            if left_labels == right_labels:
                exact_agreement_pairs[facet] += 1
                definition_comparable_pairs[facet] += 1
                if left["labelDefinitions"] == right["labelDefinitions"]:
                    definition_agreement_pairs[facet] += 1
            union = left_labels | right_labels
            jaccard_sums[facet] += (
                len(left_labels & right_labels) / len(union) if union else 1.0
            )
        if all(row["decision"] == "skip" for row in task_decisions):
            skipped += 1
            continue
        if all(row["decision"] == "pending" for row in task_decisions):
            pending += 1
            continue
        reviewers = sorted({row["reviewerId"] for row in label_votes})
        unanimous = (len(reviewers) >= minimum_independent_reviewers
                     and len(label_votes) == len(task_decisions)
                     and all(row["labels"] == label_votes[0]["labels"]
                             and row["labelDefinitions"] == label_votes[0]["labelDefinitions"]
                             for row in label_votes[1:]))
        if not unanimous:
            if len(reviewers) < minimum_independent_reviewers:
                insufficient += 1
            else:
                disagreement += 1
                disagreement_task_ids.append(task_id)
            continue
        artifact = task["artifactId"]
        source_sha, _line_count = source_cache[artifact]
        checked_evidence = []
        for vote in label_votes:
            for witness in vote["evidence"]:
                checked_evidence.append({
                    "kind": "source_span", "startLine": witness["startLine"],
                    "endLine": witness["endLine"], "sourceSha256": source_sha,
                    "reviewerId": vote["reviewerId"],
                })
        annotations.append({
            "schema": ANNOTATION_SCHEMA,
            "annotationId": f"reviewed:{task_id}",
            "artifactId": artifact,
            "sourceSha256": source_sha,
            "sourceSnapshotSha256": task["sourceSnapshotSha256"],
            "facet": facet,
            "reviewStatus": "human_adjudicated",
            "reviewerId": reviewers[0],
            "reviewerIds": reviewers,
            "independentReviewerCount": len(reviewers),
            "consensusMethod": "unanimous_exact_label_set",
            "labels": label_votes[0]["labels"],
            "labelDefinitions": label_votes[0]["labelDefinitions"],
            "labelSetComplete": True,
            "evidence": checked_evidence,
        })
        annotations_per_facet[facet] += 1
    annotations.sort(key=lambda row: (row["artifactId"], row["facet"], row["annotationId"]))
    result = {
        "schema": "info_geometry.taxonomy_adjudication_materialization_manifest.v1",
        "sourceSnapshotSha256": manifest["sourceSnapshotSha256"],
        "queueTaskRowsSha256": manifest["taskRowsSha256"],
        "decisionRowsSha256": _rows_digest(decisions),
        "annotationRowsSha256": _rows_digest(annotations),
        "queueTaskCount": len(tasks),
        "decisionCount": len(decisions),
        "humanAdjudicatedAnnotationCount": len(annotations),
        "consensusTaskCount": len(annotations),
        "consensusAnnotationsByFacet": dict(sorted(annotations_per_facet.items())),
        "skippedTaskCount": skipped,
        "pendingTaskCount": pending,
        "insufficientIndependentReviewersTaskCount": insufficient,
        "disagreementTaskCount": disagreement,
        "disagreementTaskIds": sorted(disagreement_task_ids),
        "interRaterAgreementByFacet": {
            facet: {
                "comparableLabelSetPairs": comparable_pairs[facet],
                "exactSetAgreementRate": (
                    exact_agreement_pairs[facet] / comparable_pairs[facet]
                    if comparable_pairs[facet] else None
                ),
                "meanJaccard": (
                    jaccard_sums[facet] / comparable_pairs[facet]
                    if comparable_pairs[facet] else None
                ),
                "definitionAgreementRate": (
                    definition_agreement_pairs[facet] / definition_comparable_pairs[facet]
                    if definition_comparable_pairs[facet] else None
                ),
                "definitionComparablePairs": definition_comparable_pairs[facet],
            }
            for facet in sorted({task["facet"] for task in tasks})
        },
        "unansweredTaskCount": sum(task_id not in decisions_by_task for task_id in task_by_id),
        "minimumIndependentReviewers": minimum_independent_reviewers,
        "authority": "only unanimous complete label sets from independent reviewers become training annotations",
    }
    return annotations, result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tasks", type=Path, help="taxonomy adjudication task JSONL")
    parser.add_argument("queue_manifest", type=Path)
    parser.add_argument("decisions", type=Path, help="human decision JSONL")
    parser.add_argument("--repo-root", type=Path, default=REPOSITORY_ROOT)
    parser.add_argument("--minimum-independent-reviewers", type=int, default=2)
    parser.add_argument("--out", type=Path, required=True,
                        help="reviewed annotation-v2 JSONL for corpus construction")
    parser.add_argument("--manifest-out", type=Path, required=True)
    args = parser.parse_args()
    annotations, manifest = materialize_adjudications(
        _read_jsonl(args.tasks), _read_json(args.queue_manifest),
        _read_jsonl(args.decisions), args.repo_root,
        minimum_independent_reviewers=args.minimum_independent_reviewers,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text("".join(
        json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n" for row in annotations
    ), encoding="utf-8")
    args.manifest_out.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_out.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n",
                                 encoding="utf-8")
    print(json.dumps({"annotationCount": manifest["humanAdjudicatedAnnotationCount"],
                      "pendingDecisionCount": manifest["pendingDecisionCount"],
                      "unansweredTaskCount": manifest["unansweredTaskCount"],
                      "out": str(args.out)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
