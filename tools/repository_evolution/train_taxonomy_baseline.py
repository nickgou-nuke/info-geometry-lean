#!/usr/bin/env python3
"""Fit and compare reviewed multi-label taxonomy heads across evidence views.

This CPU-capable baseline compares source embeddings, typed graph/InfoTree
features, and their fusion using the same module-held-out splits. Each view
fits train-only PCA plus balanced L2 one-vs-rest logistic heads. It consumes
only complete human-adjudicated facets and emits an inference-v3 model packet;
it never trains on weak rules or model proposals.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
from collections import Counter
from pathlib import Path
import sys
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.repository_evolution.latent_taxonomy import (
    FEATURE_VERSION,
    MODEL_SCHEMA,
    _features_for_map,
    apply_latent_expert_model,
    build_encoder_embedding_packet,
)
from tools.repository_evolution.generation_manifest import (
    validate_current_source_generation_manifest,
)
from tools.repository_evolution.reviewed_taxonomy_corpus import CORPUS_SCHEMA, LOCAL_EDGE_KINDS
from tools.repository_evolution.taxonomy_training_readiness import (
    MANIFEST_SCHEMA,
    audit_training_readiness,
)


MAP_SCHEMA = "info_geometry.refactoring_map.v1"
TRAINABLE_GRAPH_EDGE_KINDS = {
    "lean_source_import", "python_import", "lean_source_import_outside_inventory",
} & LOCAL_EDGE_KINDS


def _allowed_structural_feature(feature: str) -> bool:
    if feature.startswith(("dependency.out=", "dependency.in=")):
        return feature.split("=", 1)[1] in TRAINABLE_GRAPH_EDGE_KINDS
    if feature.startswith("dependency.walk2="):
        steps = feature.split("=", 1)[1].split(">")
        if len(steps) != 2:
            return False
        for step in steps:
            direction, separator, kind = step.partition(":")
            if (not separator or direction not in {"in", "out"}
                    or kind not in TRAINABLE_GRAPH_EDGE_KINDS):
                return False
        return True
    return feature.startswith(("declaration.kind=", "infotree.", "git.lineage."))


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        result = json.load(stream)
    if not isinstance(result, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return result


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as stream:
        rows = [json.loads(line) for line in stream if line.strip()]
    if any(not isinstance(row, dict) for row in rows):
        raise ValueError(f"{path}: each JSONL row must be an object")
    return rows


def _sigmoid_array(np: Any, logits: Any) -> Any:
    clipped = np.clip(logits, -40.0, 40.0)
    return 1.0 / (1.0 + np.exp(-clipped))


def _fit_projector(np: Any, matrix: Any, requested_dimension: int
                   ) -> tuple[Any, Any, Any, Any]:
    if matrix.ndim != 2 or matrix.shape[0] < 2 or matrix.shape[1] < 1:
        raise ValueError("training needs at least two embedding rows and one dimension")
    mean = matrix.mean(axis=0)
    scale = matrix.std(axis=0)
    scale = np.where(scale > 1e-8, scale, 1.0)
    normalized = (matrix - mean) / scale
    _, _, right = np.linalg.svd(normalized, full_matrices=False)
    dimension = min(requested_dimension, right.shape[0], matrix.shape[1], matrix.shape[0] - 1)
    if dimension < 1:
        raise ValueError("training rows have no non-constant projection dimension")
    components = right[:dimension].copy()
    # SVD permits either sign for each component. Canonicalize it for stable
    # model serialization and repeatable packet review.
    for index, component in enumerate(components):
        pivot = int(np.argmax(np.abs(component)))
        if component[pivot] < 0:
            components[index] *= -1
    projected = normalized @ components.T
    return mean, scale, components, projected


def _fit_binary_logistic(np: Any, matrix: Any, targets: Any, *, l2: float,
                         max_iterations: int, tolerance: float
                         ) -> tuple[Any, float, dict[str, Any]]:
    count, dimension = matrix.shape
    positives = int(targets.sum())
    negatives = count - positives
    if positives == 0 or negatives == 0:
        raise ValueError("each label requires both positive and negative train examples")
    sample_weights = np.where(
        targets > 0.5,
        count / (2.0 * positives),
        count / (2.0 * negatives),
    )
    augmented = np.column_stack((matrix, np.ones(count)))
    spectral_norm = float(np.linalg.norm(augmented, ord=2))
    lipschitz = 0.25 * float(sample_weights.max()) * spectral_norm**2 / count + l2
    learning_rate = 1.0 / max(lipschitz, 1e-12)
    weights = np.zeros(dimension, dtype=float)
    bias = 0.0
    converged = False
    gradient_norm = math.inf
    for iteration in range(1, max_iterations + 1):
        probabilities = _sigmoid_array(np, matrix @ weights + bias)
        residual = sample_weights * (probabilities - targets)
        gradient = matrix.T @ residual / count + l2 * weights
        bias_gradient = float(residual.mean())
        gradient_norm = max(float(np.max(np.abs(gradient))), abs(bias_gradient))
        if gradient_norm <= tolerance:
            converged = True
            break
        weights -= learning_rate * gradient
        bias -= learning_rate * bias_gradient
    if not converged:
        raise ValueError(
            f"logistic head did not converge in {max_iterations} iterations "
            f"(gradient infinity norm {gradient_norm:.3g})"
        )
    return weights, bias, {
        "iterations": iteration,
        "gradientInfinityNorm": gradient_norm,
        "positiveTrainCount": positives,
        "negativeTrainCount": negatives,
    }


def _validate_training_inputs(refactoring_map: dict[str, Any], corpus: dict[str, Any],
                              encoder_packet: dict[str, Any]) -> tuple[
                                  dict[str, dict[str, Any]], dict[str, list[float]], dict[str, Any]
                              ]:
    if refactoring_map.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    if corpus.get("schema") != MANIFEST_SCHEMA or corpus.get("corpusSchema") != CORPUS_SCHEMA:
        raise ValueError("unsupported reviewed taxonomy corpus schema")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    provenance = refactoring_map.get("analysisProvenance") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing inconsistent refactoring-map source snapshot")
    if provenance.get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("refusing inconsistent scanner/Lake analysis provenance")
    if corpus.get("sourceSnapshotSha256") != snapshot.get("pathContentManifestSha256"):
        raise ValueError("reviewed corpus and refactoring map use different source snapshots")
    if corpus.get("scannerSourceSha256") != provenance.get("scannerSourceSha256"):
        raise ValueError("reviewed corpus scanner provenance differs from refactoring map")
    if corpus.get("lakeManifestSha256") != provenance.get("lakeManifestSha256"):
        raise ValueError("reviewed corpus Lake provenance differs from refactoring map")

    file_rows = [row for row in refactoring_map.get("files", [])
                 if isinstance(row, dict) and isinstance(row.get("path"), str)]
    files = {row["path"]: row for row in file_rows}
    if len(files) != len(file_rows):
        raise ValueError("refactoring map contains duplicate artifact paths")
    expected_packet = build_encoder_embedding_packet(
        refactoring_map, encoder_packet.get("encoderVersion"),
        encoder_packet.get("embeddings"),
        encoder_training=encoder_packet.get("encoderTraining"),
    )
    if encoder_packet != expected_packet:
        raise ValueError("encoder packet is stale, malformed, or has a bad packet digest")
    vectors = {row["artifactId"]: row["vector"] for row in encoder_packet["embeddings"]}

    rows = corpus.get("rows")
    if not isinstance(rows, list):
        raise ValueError("reviewed corpus rows must be a list")
    for row in rows:
        artifact = row.get("artifactId")
        source = files.get(artifact)
        if source is None or source.get("contentSha256") != row.get("sourceSha256"):
            raise ValueError(f"reviewed corpus source hash differs from map for {artifact}")
        if artifact not in vectors:
            raise ValueError(f"encoder packet has no vector for reviewed artifact {artifact}")
        if row.get("sourceSha256") != next(
                (entry["sourceSha256"] for entry in encoder_packet["embeddings"]
                 if entry["artifactId"] == artifact), None):
            raise ValueError(f"encoder packet source hash differs for reviewed artifact {artifact}")
        if row.get("provenance", {}).get("sourceSnapshotSha256") != corpus.get(
                "sourceSnapshotSha256"):
            raise ValueError(f"reviewed row snapshot provenance differs for {artifact}")
        if row.get("provenance", {}).get("labelAuthority") != "human_adjudicated":
            raise ValueError(f"non-reviewed labels reached training input for {artifact}")
        complete_facets = row.get("labelSetCompleteByFacet", {})
        if not isinstance(complete_facets, dict) or any(
                value is not True for value in complete_facets.values()):
            raise ValueError(f"incomplete facet label set reached training input for {artifact}")
        consensus_by_facet = row.get("consensusByFacet")
        for facet in complete_facets:
            consensus = (consensus_by_facet.get(facet)
                         if isinstance(consensus_by_facet, dict) else None)
            reviewers = consensus.get("reviewerIds") if isinstance(consensus, dict) else None
            reviewer_count = (consensus.get("independentReviewerCount")
                              if isinstance(consensus, dict) else None)
            if (facet not in row.get("labels", {})
                    or not isinstance(reviewers, list) or len(reviewers) < 2
                    or any(not isinstance(reviewer, str) or not reviewer.strip()
                           or reviewer != reviewer.strip() for reviewer in reviewers)
                    or len(reviewers) != len(set(reviewers))
                    or isinstance(reviewer_count, bool)
                    or not isinstance(reviewer_count, int)
                    or reviewer_count != len(reviewers)
                    or consensus.get("method") != "unanimous_exact_label_set"):
                raise ValueError(f"independent reviewer consensus missing for {artifact}/{facet}")
    return files, vectors, expected_packet


def _training_group_digest(rows: list[dict[str, Any]]) -> str:
    groups = sorted({row["splitGroup"] for row in rows if row.get("split") == "train"})
    encoded = json.dumps(groups, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _evaluation(np: Any, rows: list[dict[str, Any]], vectors: dict[str, list[float]],
                facets: dict[str, dict[str, dict[str, Any]]], mean: Any, scale: Any,
                components: Any, split: str) -> dict[str, Any]:
    metrics_by_facet = {}
    all_tp = all_fp = all_fn = 0
    brier_sum = 0.0
    brier_count = 0
    unmodeled_positive_labels = 0
    for facet, label_models in sorted(facets.items()):
        selected = [row for row in rows
                    if row.get("split") == split and facet in row.get("labels", {})]
        if not selected:
            continue
        modeled_labels = set(label_models)
        unmodeled_positive_labels += sum(
            len(set(row["labels"][facet]) - modeled_labels)
            for row in selected
        )
        matrix = np.asarray([vectors[row["artifactId"]] for row in selected], dtype=float)
        latent = ((matrix - mean) / scale) @ components.T
        label_metrics = {}
        facet_tp = facet_fp = facet_fn = 0
        for label, head in sorted(label_models.items()):
            targets = np.asarray([
                1.0 if label in row["labels"][facet] else 0.0 for row in selected
            ])
            scores = _sigmoid_array(np, latent @ head["weights"] + head["bias"])
            predicted = scores >= 0.5
            actual = targets >= 0.5
            tp = int(np.logical_and(predicted, actual).sum())
            fp = int(np.logical_and(predicted, np.logical_not(actual)).sum())
            fn = int(np.logical_and(np.logical_not(predicted), actual).sum())
            tn = int(np.logical_and(np.logical_not(predicted), np.logical_not(actual)).sum())
            precision = tp / (tp + fp) if tp + fp else 0.0
            recall = tp / (tp + fn) if tp + fn else 0.0
            f1 = 2 * precision * recall / (precision + recall) if precision + recall else 0.0
            brier = float(np.mean((scores - targets) ** 2))
            label_metrics[label] = {
                "examples": len(selected), "positiveExamples": int(actual.sum()),
                "negativeExamples": int((~actual).sum()), "tp": tp, "fp": fp,
                "fn": fn, "tn": tn, "precisionAt05": precision,
                "recallAt05": recall, "f1At05": f1, "brierScoreUncalibrated": brier,
            }
            facet_tp += tp
            facet_fp += fp
            facet_fn += fn
            all_tp += tp
            all_fp += fp
            all_fn += fn
            brier_sum += brier
            brier_count += 1
        macro_f1 = (sum(item["f1At05"] for item in label_metrics.values())
                    / len(label_metrics))
        facet_precision = facet_tp / (facet_tp + facet_fp) if facet_tp + facet_fp else 0.0
        facet_recall = facet_tp / (facet_tp + facet_fn) if facet_tp + facet_fn else 0.0
        facet_micro_f1 = (2 * facet_precision * facet_recall / (facet_precision + facet_recall)
                          if facet_precision + facet_recall else 0.0)
        metrics_by_facet[facet] = {
            "exampleCount": len(selected), "macroF1At05": macro_f1,
            "microF1At05": facet_micro_f1, "labels": label_metrics,
        }
    precision = all_tp / (all_tp + all_fp) if all_tp + all_fp else 0.0
    recall = all_tp / (all_tp + all_fn) if all_tp + all_fn else 0.0
    micro_f1 = 2 * precision * recall / (precision + recall) if precision + recall else 0.0
    return {
        "split": split,
        "facets": metrics_by_facet,
        "microF1At05AcrossFacets": micro_f1,
        "meanBrierScoreUncalibrated": brier_sum / brier_count if brier_count else None,
        "unmodeledPositiveLabelCount": unmodeled_positive_labels,
        "scoreSemantics": "uncalibrated_sigmoid_scores_at_fixed_threshold_0.5",
    }


def _fit_reviewed_view(np: Any, rows: list[dict[str, Any]], training_rows: list[dict[str, Any]],
                       training_artifacts: list[str], vectors: dict[str, list[float]], *,
                       latent_dimension: int, l2: float, max_iterations: int,
                       tolerance: float) -> dict[str, Any]:
    """Fit one input view using train groups and evaluate untouched holdouts."""
    matrix = np.asarray([vectors[artifact] for artifact in training_artifacts], dtype=float)
    mean, scale, components, projected = _fit_projector(np, matrix, latent_dimension)
    latent_by_artifact = dict(zip(training_artifacts, projected))
    facets = sorted({facet for row in rows for facet in row["labels"]})
    fitted_facets: dict[str, dict[str, dict[str, Any]]] = {}
    fit_reports: dict[str, dict[str, Any]] = {}
    for facet in facets:
        facet_rows = [row for row in training_rows if facet in row["labels"]]
        labels = sorted({label for row in training_rows if facet in row["labels"]
                         for label in row["labels"][facet]})
        facet_matrix = np.asarray([latent_by_artifact[row["artifactId"]]
                                   for row in facet_rows], dtype=float)
        fitted_facets[facet] = {}
        fit_reports[facet] = {}
        for label in labels:
            targets = np.asarray([
                1.0 if label in row["labels"][facet] else 0.0 for row in facet_rows
            ])
            weights, bias, fit_report = _fit_binary_logistic(
                np, facet_matrix, targets, l2=l2, max_iterations=max_iterations,
                tolerance=tolerance,
            )
            fitted_facets[facet][label] = {"weights": weights, "bias": bias}
            fit_reports[facet][label] = fit_report
    return {
        "mean": mean, "scale": scale, "components": components,
        "fittedFacets": fitted_facets, "fitReports": fit_reports,
        "trainingLatentByArtifact": {
            artifact: row.astype(float).tolist()
            for artifact, row in latent_by_artifact.items()
        },
        "train": _evaluation(np, rows, vectors, fitted_facets, mean, scale,
                              components, "train"),
        "validation": _evaluation(np, rows, vectors, fitted_facets, mean, scale,
                                   components, "validation"),
        "test": _evaluation(np, rows, vectors, fitted_facets, mean, scale,
                            components, "test"),
        "trainArtifactCount": len(training_artifacts),
        "latentDimension": int(components.shape[0]),
    }


def _grouped_router_folds(training_rows: list[dict[str, Any]], *,
                          maximum_folds: int = 5) -> list[set[str]] | None:
    """Build deterministic label-balanced folds without splitting source groups."""
    labels_by_group: dict[str, set[tuple[str, str]]] = {}
    for row in training_rows:
        group = row["splitGroup"]
        labels_by_group.setdefault(group, set()).update(
            (facet, label) for facet, labels in row["labels"].items() for label in labels
        )
    groups = sorted(labels_by_group)
    if len(groups) < 2:
        return None
    label_groups: dict[tuple[str, str], set[str]] = {}
    for group, labels in labels_by_group.items():
        for label in labels:
            label_groups.setdefault(label, set()).add(group)
    fold_count = min(
        maximum_folds,
        *(min(len(group_set), len(groups) - len(group_set))
          for group_set in label_groups.values()),
    ) if label_groups else 0
    if fold_count < 2:
        return None
    fold_groups = [set() for _ in range(fold_count)]
    fold_label_counts = [Counter() for _ in range(fold_count)]
    fold_sizes = [0] * fold_count
    ordered_groups = sorted(
        groups,
        key=lambda group: (
            min((len(label_groups[label]) for label in labels_by_group[group]),
                default=len(groups)),
            -len(labels_by_group[group]), group,
        ),
    )
    totals = Counter(label for group in groups for label in labels_by_group[group])
    for group in ordered_groups:
        group_labels = labels_by_group[group]
        ideal_size = len(groups) / fold_count

        def assignment_cost(index: int) -> tuple[float, int, int]:
            label_cost = sum(
                ((fold_label_counts[index][label] + 1 - totals[label] / fold_count) ** 2)
                / max(totals[label], 1)
                for label in group_labels
            )
            size_cost = ((fold_sizes[index] + 1 - ideal_size) ** 2) / max(len(groups), 1)
            return (label_cost + 0.1 * size_cost, fold_sizes[index], index)

        selected = min(range(fold_count), key=assignment_cost)
        fold_groups[selected].add(group)
        fold_sizes[selected] += 1
        fold_label_counts[selected].update(group_labels)
    for heldout in fold_groups:
        train_groups = set(groups) - heldout
        for label, positive_groups in label_groups.items():
            positive_train = positive_groups & train_groups
            negative_train = train_groups - positive_groups
            if not positive_train or not negative_train:
                return None
    return fold_groups


def _crossfit_specialist_losses(np: Any, training_rows: list[dict[str, Any]],
                                training_artifacts: list[str], view_fits: list[tuple],
                                vectors_by_view: dict[str, dict[str, list[float]]], *,
                                latent_dimension: int, l2: float, max_iterations: int,
                                tolerance: float
                                ) -> tuple[dict[str, dict[str, float]] | None, dict[str, Any]]:
    """Predict each train artifact with specialists fit on other source groups."""
    folds = _grouped_router_folds(training_rows)
    if folds is None:
        return None, {
            "status": "in_sample_fallback",
            "reason": "not_enough_grouped_label_support_for_cross_fitting",
            "foldCount": 0,
        }
    group_by_artifact = {row["artifactId"]: row["splitGroup"] for row in training_rows}
    row_by_artifact = {row["artifactId"]: row for row in training_rows}
    losses_by_expert: dict[str, dict[str, float]] = {
        expert_id: {} for expert_id, _, _, _ in view_fits
    }
    for fold_index, heldout_groups in enumerate(folds):
        heldout_artifacts = [artifact for artifact in training_artifacts
                             if group_by_artifact[artifact] in heldout_groups]
        fit_artifacts = [artifact for artifact in training_artifacts
                         if group_by_artifact[artifact] not in heldout_groups]
        fit_rows = [row_by_artifact[artifact] for artifact in fit_artifacts]
        for expert_id, _, _, _ in view_fits:
            vectors = vectors_by_view[expert_id]
            try:
                fold_fit = _fit_reviewed_view(
                    np, fit_rows, fit_rows, fit_artifacts, vectors,
                    latent_dimension=latent_dimension, l2=l2,
                    max_iterations=max_iterations, tolerance=tolerance,
                )
            except ValueError as exc:
                return None, {
                    "status": "in_sample_fallback",
                    "reason": "fold_specialist_fit_failed",
                    "foldCount": len(folds), "failedFold": fold_index,
                    "expert": expert_id, "error": str(exc),
                }
            matrix = np.asarray([vectors[artifact] for artifact in heldout_artifacts],
                                dtype=float)
            projected = ((matrix - fold_fit["mean"]) / fold_fit["scale"]) @ (
                fold_fit["components"].T
            )
            for artifact, latent in zip(heldout_artifacts, projected):
                row = row_by_artifact[artifact]
                losses = []
                for facet, heads in fold_fit["fittedFacets"].items():
                    if facet not in row["labels"]:
                        continue
                    for label, head in heads.items():
                        logit = float(np.dot(latent, head["weights"]) + head["bias"])
                        probability = min(max(_sigmoid_array(np, logit), 1e-8), 1.0 - 1e-8)
                        target = 1.0 if label in row["labels"][facet] else 0.0
                        losses.append(-target * math.log(probability)
                                      -(1.0 - target) * math.log(1.0 - probability))
                if not losses:
                    return None, {
                        "status": "in_sample_fallback",
                        "reason": "fold_prediction_has_no_shared_train_label_vocabulary",
                        "foldCount": len(folds), "failedFold": fold_index,
                        "expert": expert_id, "artifactId": artifact,
                    }
                losses_by_expert[expert_id][artifact] = float(np.mean(losses))
    return losses_by_expert, {
        "status": "grouped_out_of_fold",
        "foldCount": len(folds),
        "folds": [sorted(fold) for fold in folds],
        "groupIsolation": True,
        "trainingArtifactCount": len(training_artifacts),
        "lossesAreOutOfFold": True,
    }


def _fit_input_router(np: Any, training_rows: list[dict[str, Any]],
                      training_artifacts: list[str], view_fits: list[tuple],
                      evidence: dict[str, list[dict[str, str]]], *,
                      target_losses_by_expert: dict[str, dict[str, float]] | None = None,
                      max_iterations: int, tolerance: float, l2: float = 0.1,
                      target_temperature: float = 0.25
                      ) -> tuple[dict[str, Any], dict[str, Any]]:
    """Distill train-only per-artifact specialist losses into a softmax router."""
    expert_ids = [item[0] for item in view_fits]
    dimensions = [len(item[1]["components"]) for item in view_fits]
    row_by_artifact = {row["artifactId"]: row for row in training_rows}
    matrix_rows, target_rows, active_rows = [], [], []
    loss_rows: dict[str, list[float]] = {expert_id: [] for expert_id in expert_ids}
    for artifact in training_artifacts:
        row = row_by_artifact[artifact]
        # Evidence is recorded for source artifacts too; the structural expert
        # is active only when a dependency, declaration, or InfoTree record exists.
        active = [
            (bool(evidence.get(artifact)) and any(
                item["kind"] != "source_artifact" for item in evidence[artifact]
            )) if expert_id == "dependency_infotree" else True
            for expert_id in expert_ids
        ]
        latent_parts = [
            item[1]["trainingLatentByArtifact"][artifact] if is_active
            else [0.0] * dimension
            for item, dimension, is_active in zip(view_fits, dimensions, active)
        ]
        matrix_rows.append([value for part in latent_parts for value in part])
        active_rows.append(active)
        losses = []
        for expert_index, (expert_id, fit, _, _) in enumerate(view_fits):
            latent = np.asarray(fit["trainingLatentByArtifact"][artifact], dtype=float)
            facet_losses = []
            for facet, heads in fit["fittedFacets"].items():
                if facet not in row["labels"]:
                    continue
                for label, head in heads.items():
                    logit = float(np.dot(latent, head["weights"]) + head["bias"])
                    probability = min(max(_sigmoid_array(np, logit), 1e-8), 1.0 - 1e-8)
                    target = 1.0 if label in row["labels"][facet] else 0.0
                    facet_losses.append(-target * math.log(probability)
                                        -(1.0 - target) * math.log(1.0 - probability))
            loss = (float(target_losses_by_expert[expert_id][artifact])
                    if target_losses_by_expert is not None else
                    float(np.mean(facet_losses)) if facet_losses else math.inf)
            losses.append(loss)
            if active[expert_index]:
                loss_rows[expert_id].append(loss)
        active_losses = [loss if is_active else math.inf
                         for loss, is_active in zip(losses, active)]
        finite_losses = [loss for loss in active_losses if math.isfinite(loss)]
        if not finite_losses:
            raise ValueError(f"no specialist has training evidence for {artifact}")
        target_logits = np.asarray([
            -loss / target_temperature if math.isfinite(loss) else -1e9
            for loss in active_losses
        ], dtype=float)
        target_logits -= target_logits.max()
        soft_targets = np.exp(target_logits)
        soft_targets /= soft_targets.sum()
        target_rows.append(soft_targets)

    matrix = np.asarray(matrix_rows, dtype=float)
    mean = matrix.mean(axis=0)
    scale = matrix.std(axis=0)
    scale = np.where(scale > 1e-8, scale, 1.0)
    normalized = (matrix - mean) / scale
    targets = np.asarray(target_rows, dtype=float)
    active_mask = np.asarray(active_rows, dtype=bool)
    count, dimension = normalized.shape
    expert_count = len(expert_ids)
    augmented = np.column_stack((normalized, np.ones(count)))
    spectral_norm = float(np.linalg.norm(augmented, ord=2))
    learning_rate = 1.0 / max(0.5 * spectral_norm**2 / count + l2, 1e-12)
    weights = np.zeros((expert_count, dimension), dtype=float)
    biases = np.zeros(expert_count, dtype=float)
    gradient_norm = math.inf
    converged = False
    for iteration in range(1, max_iterations + 1):
        logits = normalized @ weights.T + biases
        logits = np.where(active_mask, logits, -1e9)
        logits -= logits.max(axis=1, keepdims=True)
        probabilities = np.exp(logits)
        probabilities /= probabilities.sum(axis=1, keepdims=True)
        residual = (probabilities - targets) / count
        gradient = residual.T @ normalized + l2 * weights
        bias_gradient = residual.sum(axis=0)
        gradient_norm = max(float(np.max(np.abs(gradient))),
                            float(np.max(np.abs(bias_gradient))))
        if gradient_norm <= tolerance:
            converged = True
            break
        weights -= learning_rate * gradient
        biases -= learning_rate * bias_gradient
    if not converged:
        raise ValueError(
            f"router did not converge in {max_iterations} iterations "
            f"(gradient infinity norm {gradient_norm:.3g})"
        )
    router = {
        "method": "train_only_specialist_loss_distillation_softmax.v1",
        "learnsInputConditionalWeights": True,
        "trainingSplitOnly": True,
        "expertOrder": expert_ids,
        "featureMean": mean.astype(float).tolist(),
        "featureScale": scale.astype(float).tolist(),
        "weightsByExpert": {
            expert_id: weights[index].astype(float).tolist()
            for index, expert_id in enumerate(expert_ids)
        },
        "biasByExpert": {
            expert_id: float(biases[index])
            for index, expert_id in enumerate(expert_ids)
        },
        "targetTemperature": target_temperature,
    }
    report = {
        "trainingArtifactCount": count,
        "expertCount": expert_count,
        "expertInputDimensions": dict(zip(expert_ids, dimensions)),
        "routerFeatureDimension": dimension,
        "optimizer": {"iterations": iteration,
                      "gradientInfinityNorm": gradient_norm,
                      "converged": converged, "l2": l2},
        "meanTrainDistillationTargetByExpert": {
            expert_id: float(targets[:, index].mean())
            for index, expert_id in enumerate(expert_ids)
        },
        "meanTrainBinaryCrossEntropyByExpert": {
            expert_id: (float(np.mean(finite_losses)) if finite_losses else None)
            for expert_id in expert_ids
            for finite_losses in [[loss for loss in loss_rows[expert_id]
                                   if math.isfinite(loss)]]
        },
        "targetLossSource": ("grouped_out_of_fold" if target_losses_by_expert is not None
                             else "in_sample_fallback"),
        "warning": ("specialist losses are group-held-out predictions"
                    if target_losses_by_expert is not None else
                    "router uses in-sample specialist losses; held-out metrics govern usefulness"),
    }
    return router, report


def _evaluate_routed_proposals(proposals: dict[str, Any], rows: list[dict[str, Any]],
                               split: str) -> dict[str, Any]:
    """Score routed mixture probabilities on one untouched corpus split."""
    predictions = {row["artifactId"]: row for row in proposals.get("artifacts", [])}
    selected = [row for row in rows if row.get("split") == split]
    true_positive = false_positive = false_negative = 0
    brier_sum = 0.0
    brier_count = 0
    unmodeled_positive_labels = 0
    for row in selected:
        prediction = predictions.get(row["artifactId"], {})
        facets = prediction.get("combinedLabelProposalsByFacet", {})
        for facet, labels in row.get("labels", {}).items():
            scores = {item["label"]: float(item["probability"])
                      for item in facets.get(facet, [])}
            unmodeled_positive_labels += len(set(labels) - set(scores))
            label_universe = set(scores) | set(labels)
            for label in label_universe:
                probability = scores.get(label, 0.0)
                actual = label in labels
                predicted = probability >= 0.5
                true_positive += int(predicted and actual)
                false_positive += int(predicted and not actual)
                false_negative += int(not predicted and actual)
                brier_sum += (probability - float(actual)) ** 2
                brier_count += 1
    precision = (true_positive / (true_positive + false_positive)
                 if true_positive + false_positive else 0.0)
    recall = (true_positive / (true_positive + false_negative)
              if true_positive + false_negative else 0.0)
    micro_f1 = (2 * precision * recall / (precision + recall)
                if precision + recall else 0.0)
    return {
        "split": split,
        "artifactCount": len(selected),
        "microF1At05AcrossFacets": micro_f1,
        "meanBrierScoreUncalibrated": brier_sum / brier_count if brier_count else None,
        "unmodeledPositiveLabelCount": unmodeled_positive_labels,
        "scoreSemantics": "routed_mixture_of_uncalibrated_sigmoid_scores",
    }


def train_taxonomy_baseline(refactoring_map: dict[str, Any], corpus: dict[str, Any],
                            encoder_packet: dict[str, Any], *,
                            latent_dimension: int = 32, l2: float = 0.1,
                            max_iterations: int = 2000, tolerance: float = 1e-6,
                            infotree_dna: list[dict[str, Any]] | None = None,
                            infotree_dna_manifest: dict[str, Any] | None = None,
                            git_fossil_overlay_manifest: dict[str, Any] | None = None,
                            infotree_batch_reports: list[dict[str, Any]] | None = None,
                            infotree_dna_rejection_reports: list[dict[str, Any]] | None = None,
                            ) -> tuple[dict[str, Any], dict[str, Any]]:
    """Fit reviewed-label heads and report untouched validation/test metrics."""
    try:
        import numpy as np
    except ImportError as exc:  # pragma: no cover - environment-specific
        raise RuntimeError("taxonomy baseline fitting requires NumPy") from exc
    if (isinstance(latent_dimension, bool) or not isinstance(latent_dimension, int)
            or latent_dimension < 1 or isinstance(max_iterations, bool)
            or not isinstance(max_iterations, int) or max_iterations < 1
            or isinstance(l2, bool) or not isinstance(l2, (int, float))
            or not math.isfinite(float(l2)) or l2 <= 0
            or isinstance(tolerance, bool) or not isinstance(tolerance, (int, float))
            or not math.isfinite(float(tolerance)) or tolerance <= 0):
        raise ValueError("training dimensions and optimizer parameters must be positive")
    readiness = audit_training_readiness(corpus)
    if not readiness["readyForSupervisedTraining"]:
        raise ValueError(f"reviewed corpus is not trainable: {readiness['blockers']}")
    _, vectors, packet = _validate_training_inputs(refactoring_map, corpus, encoder_packet)
    rows = corpus["rows"]
    encoder_training = packet["encoderTraining"]
    data_scope = encoder_training["dataScope"]
    if data_scope == "repository_all_source":
        raise ValueError("encoder saw held-out repository source; use a train-split-only encoder")
    if data_scope == "repository_train_split":
        if encoder_training.get("sourceSnapshotSha256") != corpus.get("sourceSnapshotSha256"):
            raise ValueError("encoder training snapshot differs from reviewed corpus")
        if encoder_training.get("trainingSplitGroupsSha256") != _training_group_digest(rows):
            raise ValueError("encoder training groups differ from supervised train split")
    elif data_scope not in {"deterministic_no_training", "external_pretrained"}:
        raise ValueError("encoder training scope is unknown; refusing held-out evaluation")
    if infotree_dna is None:
        if (infotree_dna_manifest is not None or git_fossil_overlay_manifest is not None
                or infotree_batch_reports or infotree_dna_rejection_reports):
            raise ValueError("InfoTree/fossil manifests require InfoTree DNA records")
        infotree_generation_audit = {"status": "not_used"}
    else:
        if infotree_dna_manifest is None:
            raise ValueError("InfoTree DNA requires a current-source generation manifest")
        validate_current_source_generation_manifest(
            refactoring_map, infotree_dna, infotree_dna_manifest,
            git_fossil_overlay_manifest, infotree_batch_reports,
            infotree_dna_rejection_reports,
        )
        infotree_generation_audit = {
            "status": infotree_dna_manifest["coverageStatus"],
            "manifestScope": infotree_dna_manifest["manifestScope"],
            "sourceGenerationId": infotree_dna_manifest["sourceGenerationId"],
            "manifestSha256": infotree_dna_manifest["manifestSha256"],
            "expectedLeanSourceCount": infotree_dna_manifest["expectedLeanSourceCount"],
            "capturedLeanSourceCount": infotree_dna_manifest["capturedLeanSourceCount"],
            "lakeOwnerStatusCounts": infotree_dna_manifest["lakeOwnerStatusCounts"],
            "lakeBuildTargetCaptureCoverage": infotree_dna_manifest[
                "lakeBuildTargetCaptureCoverage"
            ],
            "unindexedLeanSources": infotree_dna_manifest["unindexedLeanSources"],
            "unreachableLeanModules": infotree_dna_manifest["unreachableLeanModules"],
            "missingLeanSources": infotree_dna_manifest["missingLeanSources"],
            "coverageRatio": infotree_dna_manifest["coverageRatio"],
            "captureAttemptAudit": infotree_dna_manifest["captureAttemptAudit"],
            "gitFossilOverlayBound": infotree_dna_manifest["gitFossilOverlay"] is not None,
            "gitLineageFeatureSourceCount": (
                infotree_dna_manifest["gitFossilOverlay"].get(
                    "sourceLineageFeatureSourceCount", 0
                ) if infotree_dna_manifest["gitFossilOverlay"] is not None else 0
            ),
        }
    training_rows = [row for row in rows if row["split"] == "train"]
    training_artifacts = sorted({row["artifactId"] for row in training_rows})
    raw_structural, structural_evidence = _features_for_map(
        refactoring_map, infotree_dna, git_fossil_overlay_manifest
    )
    allowed_features = sorted({
        feature for artifact in training_artifacts
        for feature, value in raw_structural.get(artifact, {}).items()
        if _allowed_structural_feature(feature) and value > 0
    })
    allowed_feature_set = set(allowed_features)
    structural_vectors = {
        artifact: {feature: math.log1p(float(value))
                   for feature, value in raw_structural.get(artifact, {}).items()
                   if feature in allowed_feature_set and value > 0}
        for artifact in vectors
    }
    structural_training_payload = [
        {"artifactId": artifact, "features": dict(sorted(structural_vectors[artifact].items()))}
        for artifact in training_artifacts
    ]
    structural_training_sha256 = hashlib.sha256(json.dumps(
        structural_training_payload, sort_keys=True, ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")).hexdigest()
    encoder_dimension = len(vectors[training_artifacts[0]])
    combined_vectors = {
        artifact: [*vectors[artifact], *[
            structural_vectors[artifact].get(feature, 0.0) for feature in allowed_features
        ]]
        for artifact in vectors
    }
    source_vectors = {artifact: vectors[artifact] for artifact in vectors}
    structural_only_vectors = {
        artifact: [structural_vectors[artifact].get(feature, 0.0)
                   for feature in allowed_features]
        for artifact in vectors
    }
    source_fit = _fit_reviewed_view(
        np, rows, training_rows, training_artifacts, source_vectors,
        latent_dimension=latent_dimension, l2=l2, max_iterations=max_iterations,
        tolerance=tolerance,
    )
    fused_fit = _fit_reviewed_view(
        np, rows, training_rows, training_artifacts, combined_vectors,
        latent_dimension=latent_dimension, l2=l2, max_iterations=max_iterations,
        tolerance=tolerance,
    )
    structure_fit = None
    if allowed_features:
        structure_fit = _fit_reviewed_view(
            np, rows, training_rows, training_artifacts, structural_only_vectors,
            latent_dimension=latent_dimension, l2=l2, max_iterations=max_iterations,
            tolerance=tolerance,
        )
    lineage_features = [feature for feature in allowed_features
                        if feature.startswith("git.lineage.")]
    non_lineage_features = [feature for feature in allowed_features
                            if not feature.startswith("git.lineage.")]
    lineage_ablation_fit = None
    if lineage_features:
        lineage_ablation_vectors = {
            artifact: [*vectors[artifact], *[
                structural_vectors[artifact].get(feature, 0.0)
                for feature in non_lineage_features
            ]]
            for artifact in vectors
        }
        lineage_ablation_fit = _fit_reviewed_view(
            np, rows, training_rows, training_artifacts, lineage_ablation_vectors,
            latent_dimension=latent_dimension, l2=l2, max_iterations=max_iterations,
            tolerance=tolerance,
        )
    mean = fused_fit["mean"]
    scale = fused_fit["scale"]
    components = fused_fit["components"]
    fitted_facets = fused_fit["fittedFacets"]
    fit_reports = fused_fit["fitReports"]
    latent_size = int(components.shape[0])
    source_components = components[:, :encoder_dimension]
    structural_components = components[:, encoder_dimension:]
    structural_projection = []
    projection_bias = []
    for component in structural_components:
        structural_projection.append({
            feature: float(weight / feature_scale)
            for feature, weight, feature_scale in zip(
                allowed_features, component, scale[encoder_dimension:]
            )
            if abs(float(weight / feature_scale)) > 1e-15
        })
        projection_bias.append(float(-np.sum(
            (mean[encoder_dimension:] / scale[encoder_dimension:]) * component
        )))
    infotree_records = infotree_dna or []
    training_infotree_records = [
        record for record in infotree_records
        if isinstance(record, dict) and record.get("artifactId") in training_artifacts
    ]
    infotree_capture_payload = [{
        key: record.get(key) for key in (
            "artifactId", "sourceSha256", "featureVersion", "leanContextFingerprint",
            "rawCaptureSha256", "dnaFingerprint", "features", "captureLossless",
            "leakageRowCount", "status",
        )
    } for record in sorted(training_infotree_records,
                            key=lambda item: item.get("artifactId", ""))]
    infotree_capture_sha256 = hashlib.sha256(json.dumps(
        infotree_capture_payload, sort_keys=True, ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")).hexdigest()

    # Keep a distinct projector and set of heads for every evidence view. The
    # inference packet can then omit a missing view without silently applying
    # a fused classifier to a source-only or graph-only representation.
    view_fits = [("source_embedding", source_fit, source_vectors, "source")]
    if structure_fit is not None:
        view_fits.append(("dependency_infotree", structure_fit,
                          structural_only_vectors, "structure"))
    view_fits.append(("source_structure_fused", fused_fit, combined_vectors, "fused"))
    vectors_by_view = {expert_id: view_vectors
                       for expert_id, _, view_vectors, _ in view_fits}
    router_target_losses, router_crossfit_report = _crossfit_specialist_losses(
        np, training_rows, training_artifacts, view_fits, vectors_by_view,
        latent_dimension=latent_dimension, l2=l2,
        max_iterations=max_iterations, tolerance=tolerance,
    )
    router_model, router_report = _fit_input_router(
        np, training_rows, training_artifacts, view_fits, structural_evidence,
        target_losses_by_expert=router_target_losses,
        max_iterations=max_iterations, tolerance=tolerance,
    )
    router_report["crossFit"] = router_crossfit_report

    def serialize_view(fit: dict[str, Any], view_kind: str) -> dict[str, Any]:
        view_components = fit["components"]
        view_mean = fit["mean"]
        view_scale = fit["scale"]
        if view_kind == "source":
            feature_names: list[str] = []
            feature_components = np.zeros((len(view_components), 0), dtype=float)
            encoder_components = view_components
            encoder_mean = view_mean
            encoder_scale = view_scale
        elif view_kind == "structure":
            feature_names = allowed_features
            feature_components = view_components
            encoder_components = None
            encoder_mean = encoder_scale = None
        else:
            feature_names = allowed_features
            feature_components = view_components[:, encoder_dimension:]
            encoder_components = view_components[:, :encoder_dimension]
            encoder_mean = view_mean[:encoder_dimension]
            encoder_scale = view_scale[:encoder_dimension]
        feature_projection = []
        feature_bias = []
        for component in feature_components:
            feature_projection.append({
                feature: float(weight / feature_scale)
                for feature, weight, feature_scale in zip(
                    feature_names, component,
                    view_scale[-len(feature_names):] if feature_names else [],
                )
                if abs(float(weight / feature_scale)) > 1e-15
            })
            feature_bias.append(float(-np.sum(
                (view_mean[-len(feature_names):] / view_scale[-len(feature_names):])
                * component
            )) if feature_names else 0.0)
        return {
            "projection": feature_projection,
            "projectionBias": feature_bias,
            "encoderProjection": (encoder_components.astype(float).tolist()
                                  if encoder_components is not None else None),
            "encoderNormalization": ({
                "mean": encoder_mean.astype(float).tolist(),
                "scale": encoder_scale.astype(float).tolist(),
            } if encoder_mean is not None else None),
        }

    train_briers = {
        expert_id: fit["train"].get("meanBrierScoreUncalibrated")
        for expert_id, fit, _, _ in view_fits
    }
    experts = []
    for expert_id, fit, _, view_kind in view_fits:
        view = serialize_view(fit, view_kind)
        experts.append({
            "id": expert_id,
            "version": "train_only_pca_balanced_l2_ovr_logistic.v1",
            "inputView": view_kind,
            "viewProjection": view,
            "gateBias": 0.0,
            "gateWeights": [0.0] * len(fit["components"]),
            "gateTrainingEvidence": {
                "method": router_model["method"],
                "trainMeanBrierScoreUncalibrated": train_briers[expert_id],
                "routerFit": "see trainingReport.routerTraining",
            },
            "evidenceKinds": (
                ["source_artifact"] if view_kind == "source" else
                ["dependency_edge", "lexical_declaration_candidate", "infotree_dna"]
                if view_kind == "structure" else
                ["source_artifact", "dependency_edge",
                 "lexical_declaration_candidate", "infotree_dna"]
            ),
            "labelHeadsByFacet": {
                facet: {
                    label: {
                        "bias": float(head["bias"]),
                        "weights": head["weights"].astype(float).tolist(),
                    }
                    for label, head in sorted(label_heads.items())
                }
                for facet, label_heads in sorted(fit["fittedFacets"].items())
            },
        })
    model = {
        "schema": MODEL_SCHEMA,
        "modelVersion": "reviewed_multiview_pca_ovr_logistic_input_router.v4",
        "featureVersion": FEATURE_VERSION,
        "featureVocabulary": allowed_features,
        "projection": structural_projection,
        "projectionBias": projection_bias,
        "encoderSpec": {
            "version": packet["encoderVersion"],
            "dimension": packet["embeddingDimension"],
        },
        "encoderNormalization": {
            "mean": mean[:encoder_dimension].astype(float).tolist(),
            "scale": scale[:encoder_dimension].astype(float).tolist(),
        },
        "encoderProjection": source_components.astype(float).tolist(),
        "experts": experts,
        "router": router_model,
        "minimumLabelProbability": 0.5,
        "minimumLabelMargin": 0.0,
        "trainingMethod": "train_only_multiview_pca_balanced_l2_ovr_logistic_with_oof_router.v5",
        "structuralFeaturePolicy": "typed_dependencies_declarations_infotree_verified_git_lineage.v2",
        "trainingStructuralFeatureVocabulary": allowed_features,
        "trainingStructuralInputsSha256": structural_training_sha256,
        "trainingInfoTreeCaptureSha256": infotree_capture_sha256,
        "trainingInfoTreeGenerationAudit": infotree_generation_audit,
        "trainingInfoTreeCaptureAudit": {
            "trainingArtifactRecords": len(training_infotree_records),
            "losslessCaptureCount": sum(record.get("captureLossless") is True
                                         for record in training_infotree_records),
            "partialCaptureCount": sum(record.get("captureLossless") is not True
                                        for record in training_infotree_records),
            "leakageRowCount": sum(int(record.get("leakageRowCount", 0) or 0)
                                    for record in training_infotree_records),
            "authority": "capture-quality metadata; not semantic truth",
        },
        "trainingDataSnapshotRefs": [corpus["sourceSnapshotSha256"]],
        "trainingCorpusRowsSha256": corpus["corpusRowsSha256"],
        "trainingEncoderPacketSha256": packet["packetSha256"],
        "encoderTraining": encoder_training,
        "trainingHyperparameters": {
            "latentDimensionRequested": latent_dimension,
            "latentDimensionUsed": latent_size,
            "l2": l2,
            "maxIterations": max_iterations,
            "tolerance": tolerance,
            "classWeighting": "balanced_positive_negative",
            "randomSeed": None,
        },
    }
    routed_proposals = apply_latent_expert_model(
        refactoring_map, model, infotree_dna, packet, git_fossil_overlay_manifest
    )
    report = {
        "schema": "info_geometry.taxonomy_model_training_report.v1",
        "modelSchema": MODEL_SCHEMA,
        "modelVersion": model["modelVersion"],
        "sourceSnapshotSha256": corpus["sourceSnapshotSha256"],
        "corpusRowsSha256": corpus["corpusRowsSha256"],
        "encoderPacketSha256": packet["packetSha256"],
        "encoderTraining": encoder_training,
        "readiness": readiness,
        "trainArtifactCount": len(training_artifacts),
        "trainingStructuralFeatureCount": len(allowed_features),
        "trainingStructuralInputsSha256": structural_training_sha256,
        "trainingInfoTreeCaptureSha256": infotree_capture_sha256,
        "trainingInfoTreeGenerationAudit": infotree_generation_audit,
        "trainingInfoTreeCaptureAudit": model["trainingInfoTreeCaptureAudit"],
        "labelFitReports": fit_reports,
        "expertTraining": {
            expert_id: {
                "train": fit["train"], "validation": fit["validation"],
                "test": fit["test"],
            }
            for expert_id, fit, _, _ in view_fits
        },
        "routerTraining": router_report,
        "validation": fused_fit["validation"],
        "test": fused_fit["test"],
        "routedValidation": _evaluate_routed_proposals(
            routed_proposals, rows, "validation"
        ),
        "routedTest": _evaluate_routed_proposals(routed_proposals, rows, "test"),
        "viewAblations": {
            "sourceOnly": {
                "trainingFeatureCount": len(vectors[training_artifacts[0]]),
                "validation": source_fit["validation"], "test": source_fit["test"],
            },
            "structureOnly": ({
                "trainingFeatureCount": len(allowed_features),
                "validation": structure_fit["validation"], "test": structure_fit["test"],
            } if structure_fit else {
                "status": "not_available_no_reviewed_train_graph_features",
                "validation": None, "test": None,
            }),
            "sourceAndStructure": {
                "trainingFeatureCount": len(vectors[training_artifacts[0]]) + len(allowed_features),
                "validation": fused_fit["validation"], "test": fused_fit["test"],
            },
            "sourceAndStructureWithoutGitLineage": ({
                "trainingFeatureCount": len(vectors[training_artifacts[0]])
                                        + len(non_lineage_features),
                "removedGitLineageFeatureCount": len(lineage_features),
                "validation": lineage_ablation_fit["validation"],
                "test": lineage_ablation_fit["test"],
            } if lineage_ablation_fit else {
                "status": "not_applicable_no_git_lineage_features",
                "removedGitLineageFeatureCount": 0,
                "validation": None,
                "test": None,
            }),
            "comparisonPolicy": "same_reviewed_rows_and_group_holdouts; train-only_scalers_and_projection",
            "testSetPolicy": "descriptive_comparison_only; select_method_on_validation_and_avoid_repeated_test_tuning",
        },
        "authority": "human-adjudicated complete labels; fit split only; validation/test are evaluation only",
    }
    return model, report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("reviewed_corpus_manifest", type=Path)
    parser.add_argument("encoder_embeddings", type=Path)
    parser.add_argument("--infotree-dna", type=Path,
                        help="optional source-bound structural InfoTree DNA JSONL")
    parser.add_argument("--infotree-dna-manifest", type=Path,
                        help="generation receipt emitted by generation_manifest.py")
    parser.add_argument("--git-fossil-overlay-manifest", type=Path,
                        help="optional validated Git-fossil overlay metadata.json")
    parser.add_argument("--infotree-batch-report", type=Path, action="append", default=[],
                        help="batch capture attempt report; may be repeated")
    parser.add_argument("--infotree-dna-rejections", type=Path, action="append", default=[],
                        help="audited DNA rejection report; may be repeated")
    parser.add_argument("--latent-dimension", type=int, default=32)
    parser.add_argument("--l2", type=float, default=0.1)
    parser.add_argument("--max-iterations", type=int, default=2000)
    parser.add_argument("--tolerance", type=float, default=1e-6)
    parser.add_argument("--model-out", type=Path, required=True)
    parser.add_argument("--report-out", type=Path, required=True)
    args = parser.parse_args()
    model, report = train_taxonomy_baseline(
        _read_json(args.refactoring_map), _read_json(args.reviewed_corpus_manifest),
        _read_json(args.encoder_embeddings), latent_dimension=args.latent_dimension,
        l2=args.l2, max_iterations=args.max_iterations, tolerance=args.tolerance,
        infotree_dna=_read_jsonl(args.infotree_dna) if args.infotree_dna else None,
        infotree_dna_manifest=(_read_json(args.infotree_dna_manifest)
                               if args.infotree_dna_manifest else None),
        git_fossil_overlay_manifest=(
            _read_json(args.git_fossil_overlay_manifest)
            if args.git_fossil_overlay_manifest else None
        ),
        infotree_batch_reports=[_read_json(path) for path in args.infotree_batch_report],
        infotree_dna_rejection_reports=[
            _read_json(path) for path in args.infotree_dna_rejections
        ],
    )
    for path, value in ((args.model_out, model), (args.report_out, report)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, sort_keys=True, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    print(json.dumps({
        "modelOut": str(args.model_out), "reportOut": str(args.report_out),
        "testMicroF1At05": report["test"]["microF1At05AcrossFacets"],
        "latentDimension": report["labelFitReports"] and model[
            "trainingHyperparameters"]["latentDimensionUsed"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
