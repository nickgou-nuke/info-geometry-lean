#!/usr/bin/env python3
"""Audit whether a reviewed taxonomy corpus can support supervised training.

This is a data-quality gate, not a trainer. It checks corpus integrity, group
split isolation, and per-facet label coverage before model fitting is attempted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


CORPUS_SCHEMA = "info_geometry.reviewed_taxonomy_corpus.v4"
MANIFEST_SCHEMA = "info_geometry.reviewed_taxonomy_corpus_manifest.v4"
LABEL_CODEBOOK_SCHEMA = "info_geometry.taxonomy_label_codebook.v1"
SPLITS = ("train", "validation", "test")


def _canonical_rows_digest(rows: list[dict[str, Any]]) -> str:
    payload = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
        for row in rows
    )
    return hashlib.sha256(payload).hexdigest()


def _is_sha256(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    try:
        int(value, 16)
    except ValueError:
        return False
    return True


def audit_training_readiness(corpus: dict[str, Any], *,
                             minimum_train_examples_per_label: int = 2,
                             minimum_train_groups_per_label: int = 2
                             ) -> dict[str, Any]:
    """Return an explicit readiness report without changing the corpus.

    A label is considered evaluable only when it occurs in both validation and
    test. Groups are module/owner holdout units and may occur in exactly one
    split. Training support is counted both by rows and by independent groups;
    repeated artifacts from one group do not count as independent positives.
    Insufficient data is reported as a blocker rather than an exception.
    """
    if corpus.get("corpusSchema") != CORPUS_SCHEMA:
        raise ValueError(f"expected corpusSchema {CORPUS_SCHEMA}")
    if corpus.get("schema") != MANIFEST_SCHEMA:
        raise ValueError(f"expected schema {MANIFEST_SCHEMA}")
    if (isinstance(minimum_train_examples_per_label, bool)
            or not isinstance(minimum_train_examples_per_label, int)
            or minimum_train_examples_per_label < 1):
        raise ValueError("minimum_train_examples_per_label must be a positive integer")
    if (isinstance(minimum_train_groups_per_label, bool)
            or not isinstance(minimum_train_groups_per_label, int)
            or minimum_train_groups_per_label < 1):
        raise ValueError("minimum_train_groups_per_label must be a positive integer")
    rows = corpus.get("rows")
    if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
        raise ValueError("corpus rows must be a list of objects")

    blockers: list[str] = []
    if corpus.get("corpusRowsSha256") != _canonical_rows_digest(rows):
        blockers.append("corpus_rows_digest_mismatch")
    if corpus.get("artifactCount") != len(rows):
        blockers.append("artifact_count_mismatch")

    artifacts: set[str] = set()
    group_split: dict[str, str] = {}
    content_hash_split: dict[str, str] = {}
    split_rows: Counter[str] = Counter()
    facet_label_counts: dict[str, dict[str, Counter[str]]] = defaultdict(
        lambda: {split: Counter() for split in SPLITS}
    )
    facet_example_counts: dict[str, Counter[str]] = defaultdict(Counter)
    facet_group_splits: dict[str, dict[str, str]] = defaultdict(dict)
    facet_group_labels: dict[str, dict[str, set[str]]] = defaultdict(
        lambda: defaultdict(set)
    )
    observed_codebook: dict[tuple[str, str], str] = {}
    malformed_rows = []
    for index, row in enumerate(rows):
        artifact = row.get("artifactId")
        source_hash = row.get("sourceSha256")
        group = row.get("splitGroup")
        split = row.get("split")
        labels = row.get("labels")
        definitions_by_facet = row.get("labelDefinitionsByFacet")
        if (not isinstance(artifact, str) or not artifact
                or not _is_sha256(source_hash)
                or not isinstance(group, str) or not group
                or split not in SPLITS or not isinstance(labels, dict)):
            malformed_rows.append(index)
            continue
        # Validate before set/dict operations or coverage accounting. JSON
        # arrays/objects are not hashable labels, and duplicate entries must
        # not silently become a reviewed set through deduplication.
        if any(
            not isinstance(facet, str) or not facet
            or not isinstance(values, list)
            or any(not isinstance(value, str) or not value
                   or value != value.strip() for value in values)
            or len(values) != len(set(values))
            for facet, values in labels.items()
        ):
            malformed_rows.append(index)
            continue
        if artifact in artifacts:
            blockers.append("duplicate_artifact_rows")
        artifacts.add(artifact)
        previous_split = group_split.setdefault(group, split)
        if previous_split != split:
            blockers.append("split_group_leakage")
        previous_content_split = content_hash_split.setdefault(source_hash, split)
        if previous_content_split != split:
            blockers.append("duplicate_source_hash_split_leakage")
        split_rows[split] += 1
        complete_facets = row.get("labelSetCompleteByFacet")
        consensus_by_facet = row.get("consensusByFacet")
        if not isinstance(complete_facets, dict):
            blockers.append("incomplete_label_set_semantics")
            malformed_rows.append(index)
            continue
        if not isinstance(definitions_by_facet, dict):
            blockers.append("label_codebook_malformed")
            malformed_rows.append(index)
            definitions_by_facet = {}
        elif set(definitions_by_facet) != set(complete_facets):
            blockers.append("label_codebook_malformed")
            malformed_rows.append(index)
        for facet, is_complete in complete_facets.items():
            if not isinstance(facet, str) or not facet or is_complete is not True:
                blockers.append("incomplete_label_set_semantics")
                continue
            if facet not in labels:
                blockers.append("incomplete_label_set_semantics")
                malformed_rows.append(index)
                continue
            facet_labels = labels.get(facet)
            definitions = definitions_by_facet.get(facet)
            if (not isinstance(facet_labels, list) or not isinstance(definitions, dict)
                    or set(definitions) != set(facet_labels)
                    or any(not isinstance(value, str) or len(value.split()) < 2
                           or value != " ".join(value.split())
                           for value in definitions.values())):
                blockers.append("label_codebook_malformed")
                malformed_rows.append(index)
            elif isinstance(facet_labels, list):
                for label, definition in definitions.items():
                    key = (facet, label)
                    previous = observed_codebook.setdefault(key, definition)
                    if previous != definition:
                        blockers.append("conflicting_label_definitions")
            consensus = (consensus_by_facet.get(facet)
                         if isinstance(consensus_by_facet, dict) else None)
            reviewer_ids = consensus.get("reviewerIds") if isinstance(consensus, dict) else None
            count = consensus.get("independentReviewerCount") if isinstance(consensus, dict) else None
            if (not isinstance(reviewer_ids, list) or len(reviewer_ids) < 2
                    or any(not isinstance(reviewer, str) or not reviewer.strip()
                           or reviewer != reviewer.strip() for reviewer in reviewer_ids)
                    or len(reviewer_ids) != len(set(reviewer_ids))
                    or isinstance(count, bool) or not isinstance(count, int)
                    or count != len(reviewer_ids)
                    or consensus.get("method") != "unanimous_exact_label_set"):
                blockers.append("insufficient_independent_review_consensus")
            facet_example_counts[facet][split] += 1
            previous_group_split = facet_group_splits[facet].setdefault(group, split)
            if previous_group_split != split:
                blockers.append("split_group_leakage")
        for facet, values in labels.items():
            if (not isinstance(facet, str) or not facet or not isinstance(values, list)
                    or any(not isinstance(value, str) or not value or value != value.strip()
                                         for value in values)):
                malformed_rows.append(index)
                continue
            if complete_facets.get(facet) is not True:
                blockers.append("incomplete_label_set_semantics")
            facet_label_counts[facet][split].update(set(values))
            if complete_facets.get(facet) is True:
                facet_group_labels[facet][group].update(values)

    if malformed_rows:
        blockers.append("malformed_rows")

    observed_codebook_rows = [
        {"facet": facet, "label": label, "definition": definition}
        for (facet, label), definition in sorted(observed_codebook.items())
    ]
    declared_codebook = corpus.get("labelCodebook")
    declared_codebook_schema = corpus.get("labelCodebookSchema")
    canonical_codebook = {"schema": LABEL_CODEBOOK_SCHEMA,
                          "labels": observed_codebook_rows}
    expected_codebook_digest = hashlib.sha256(json.dumps(
        canonical_codebook, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")).hexdigest()
    if (declared_codebook_schema != LABEL_CODEBOOK_SCHEMA
            or declared_codebook != observed_codebook_rows
            or corpus.get("labelCodebookSha256") != expected_codebook_digest):
        blockers.append("label_codebook_digest_or_catalog_mismatch")
    missing_splits = [split for split in SPLITS if split_rows[split] == 0]
    if missing_splits:
        blockers.append("missing_required_splits")

    label_coverage: dict[str, dict[str, dict[str, int]]] = {}
    label_group_coverage: dict[str, dict[str, dict[str, dict[str, int]]]] = {}
    underrepresented: list[dict[str, Any]] = []
    underrepresented_groups: list[dict[str, Any]] = []
    unevaluated: list[dict[str, Any]] = []
    no_negative_training_examples: list[dict[str, Any]] = []
    no_negative_evaluation_examples: list[dict[str, Any]] = []
    no_negative_training_groups: list[dict[str, Any]] = []
    no_negative_evaluation_groups: list[dict[str, Any]] = []
    for facet in sorted(facet_label_counts):
        label_coverage[facet] = {}
        label_group_coverage[facet] = {}
        labels = set().union(*(set(facet_label_counts[facet][split]) for split in SPLITS))
        group_totals = Counter(facet_group_splits[facet].values())
        for label in sorted(labels):
            counts = {split: facet_label_counts[facet][split][label] for split in SPLITS}
            label_coverage[facet][label] = counts
            if counts["train"] < minimum_train_examples_per_label:
                underrepresented.append({"facet": facet, "label": label,
                                         "trainingExamples": counts["train"]})
            if counts["validation"] == 0 or counts["test"] == 0:
                unevaluated.append({"facet": facet, "label": label,
                                    "validationExamples": counts["validation"],
                                    "testExamples": counts["test"]})
            negatives = {
                split: facet_example_counts[facet][split] - counts[split]
                for split in SPLITS
            }
            if negatives["train"] == 0:
                no_negative_training_examples.append({"facet": facet, "label": label})
            if negatives["validation"] == 0 or negatives["test"] == 0:
                no_negative_evaluation_examples.append({
                    "facet": facet, "label": label,
                    "validationNegativeExamples": negatives["validation"],
                    "testNegativeExamples": negatives["test"],
                })
            positive_groups = Counter(
                group_split for group, group_split in facet_group_splits[facet].items()
                if label in facet_group_labels[facet].get(group, set())
            )
            group_counts = {split: positive_groups[split] for split in SPLITS}
            label_group_coverage[facet][label] = {
                split: {
                    "positiveGroups": group_counts[split],
                    "negativeGroups": group_totals[split] - group_counts[split],
                }
                for split in SPLITS
            }
            if group_counts["train"] < minimum_train_groups_per_label:
                underrepresented_groups.append({
                    "facet": facet, "label": label,
                    "trainingGroups": group_counts["train"],
                })
            negative_group_counts = {
                split: group_totals[split] - group_counts[split] for split in SPLITS
            }
            if negative_group_counts["train"] == 0:
                no_negative_training_groups.append({"facet": facet, "label": label})
            if (negative_group_counts["validation"] == 0
                    or negative_group_counts["test"] == 0):
                no_negative_evaluation_groups.append({
                    "facet": facet, "label": label,
                    "validationNegativeGroups": negative_group_counts["validation"],
                    "testNegativeGroups": negative_group_counts["test"],
                })
    if not label_coverage:
        blockers.append("no_reviewed_labels")
    if underrepresented:
        blockers.append("labels_below_minimum_training_count")
    if underrepresented_groups:
        blockers.append("labels_below_minimum_independent_training_groups")
    if unevaluated:
        blockers.append("labels_missing_validation_or_test_coverage")
    if no_negative_training_examples:
        blockers.append("labels_missing_negative_training_examples")
    if no_negative_evaluation_examples:
        blockers.append("labels_missing_negative_evaluation_examples")
    if no_negative_training_groups:
        blockers.append("labels_missing_negative_training_groups")
    if no_negative_evaluation_groups:
        blockers.append("labels_missing_negative_evaluation_groups")

    declared_splits = corpus.get("splitCounts")
    observed_splits = {split: split_rows[split] for split in SPLITS}
    if declared_splits != observed_splits:
        blockers.append("split_count_mismatch")
    return {
        "schema": "info_geometry.taxonomy_training_readiness.v1",
        "readyForSupervisedTraining": not blockers,
        "blockers": sorted(set(blockers)),
        "artifactCount": len(artifacts),
        "malformedRowIndices": sorted(set(malformed_rows)),
        "observedSplitCounts": observed_splits,
        "groupCount": len(group_split),
        "labelCoverageByFacet": label_coverage,
        "labelGroupCoverageByFacet": label_group_coverage,
        "underrepresentedLabels": underrepresented,
        "labelsBelowMinimumIndependentTrainingGroups": underrepresented_groups,
        "labelsMissingEvaluationCoverage": unevaluated,
        "labelsMissingNegativeTrainingExamples": no_negative_training_examples,
        "labelsMissingNegativeEvaluationExamples": no_negative_evaluation_examples,
        "labelsMissingNegativeTrainingGroups": no_negative_training_groups,
        "labelsMissingNegativeEvaluationGroups": no_negative_evaluation_groups,
        "minimumTrainExamplesPerLabel": minimum_train_examples_per_label,
        "minimumTrainGroupsPerLabel": minimum_train_groups_per_label,
        "corpusRowsSha256Verified": corpus.get("corpusRowsSha256")
        == _canonical_rows_digest(rows),
        "authority": "data readiness only; no model was trained or validated",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus_manifest", type=Path)
    parser.add_argument("--minimum-train-examples-per-label", type=int, default=2)
    parser.add_argument("--minimum-train-groups-per-label", type=int, default=2)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    corpus = json.loads(args.corpus_manifest.read_text(encoding="utf-8"))
    report = audit_training_readiness(
        corpus,
        minimum_train_examples_per_label=args.minimum_train_examples_per_label,
        minimum_train_groups_per_label=args.minimum_train_groups_per_label,
    )
    rendered = json.dumps(report, sort_keys=True, ensure_ascii=False, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0 if report["readyForSupervisedTraining"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
