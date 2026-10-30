#!/usr/bin/env python3
"""Train a small two-direction, relation-aware graph context encoder.

The encoder is a self-supervised stage between source embedding extraction and
reviewed-taxonomy fitting. It learns to reconstruct a masked source embedding
from typed dependency neighbors. Training uses only artifacts and edges inside
the reviewed corpus's train groups; inference applies the learned encoder to
the complete current graph. Consequently this is an inductive train /
transductive current-graph representation, not a causal or semantic proof.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import random
from pathlib import Path
import sys
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.repository_evolution.attention_scc import DEPENDENCY_KINDS
from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet
from tools.repository_evolution.taxonomy_training_readiness import audit_training_readiness
from tools.repository_evolution.train_code_transformer import _train_group_digest


MODEL_VERSION = "typed_bidirectional_graph_denoiser.v3"


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "wt", encoding="utf-8") as stream:
        stream.write(json.dumps(value, sort_keys=True, ensure_ascii=False) + "\n")


def _validate_inputs(
        refactoring_map: dict[str, Any], corpus: dict[str, Any],
        source_packet: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, list[float]], str]:
    if refactoring_map.get("schema") != "info_geometry.refactoring_map.v1":
        raise ValueError("unsupported refactoring-map schema")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing an inconsistent source-map snapshot")
    if (refactoring_map.get("analysisProvenance", {}).get(
            "analysisInputsConsistentDuringScan") is not True):
        raise ValueError("refusing inconsistent scanner/Lake provenance")
    if corpus.get("sourceSnapshotSha256") != snapshot.get("pathContentManifestSha256"):
        raise ValueError("reviewed corpus and source map refer to different snapshots")
    readiness = audit_training_readiness(corpus)
    if not readiness["readyForSupervisedTraining"]:
        raise ValueError(f"reviewed corpus is not ready: {readiness['blockers']}")

    rebuilt = build_encoder_embedding_packet(
        refactoring_map, source_packet.get("encoderVersion"),
        source_packet.get("embeddings"),
        encoder_training=source_packet.get("encoderTraining"),
    )
    if source_packet != rebuilt:
        raise ValueError("source embedding packet is stale, malformed, or has a bad digest")
    if source_packet.get("sourceSnapshotSha256") != corpus.get("sourceSnapshotSha256"):
        raise ValueError("source embeddings and reviewed corpus refer to different snapshots")

    train_rows = [row for row in corpus["rows"] if row.get("split") == "train"]
    if len(train_rows) < 2:
        raise ValueError("graph denoising requires at least two train artifacts")
    for row in train_rows:
        if row.get("provenance", {}).get("labelAuthority") != "human_adjudicated":
            raise ValueError("non-reviewed corpus row reached graph-encoder training")
    source_vectors = {
        row["artifactId"]: row["vector"] for row in source_packet["embeddings"]
    }
    map_hashes = {
        row["path"]: row.get("contentSha256")
        for row in refactoring_map.get("files", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }
    for row in source_packet["embeddings"]:
        path = row["artifactId"]
        if row["sourceSha256"] != map_hashes.get(path):
            raise ValueError(f"source embedding hash differs from map for {path}")

    train_ids = {row["artifactId"] for row in train_rows}
    missing = sorted(train_ids - set(source_vectors))
    if missing:
        raise ValueError("source packet lacks train artifacts: " + ", ".join(missing[:5]))
    train_groups_digest = _train_group_digest(corpus["rows"])
    base_training = source_packet.get("encoderTraining", {})
    if base_training.get("dataScope") == "repository_train_split":
        if (base_training.get("sourceSnapshotSha256") != corpus.get("sourceSnapshotSha256")
                or base_training.get("trainingSplitGroupsSha256") != train_groups_digest):
            raise ValueError("source encoder training groups differ from reviewed corpus")
    elif base_training.get("dataScope") not in {
            "deterministic_no_training", "external_pretrained"}:
        raise ValueError("source encoder provenance is unknown or includes held-out source")
    return train_rows, source_vectors, train_groups_digest


def _edge_index(
        refactoring_map: dict[str, Any], nodes: list[str], *, induced: set[str] | None = None
        ) -> dict[str, list[tuple[int, int]]]:
    index = {path: position for position, path in enumerate(nodes)}
    result = {kind: [] for kind in sorted(DEPENDENCY_KINDS)}
    seen: set[tuple[str, str, str]] = set()
    for edge in refactoring_map.get("dependencyEdges", []):
        if not isinstance(edge, dict):
            continue
        source, target, kind = edge.get("from"), edge.get("to"), edge.get("kind")
        if (kind not in result or source not in index or target not in index
                or (induced is not None and (source not in induced or target not in induced))):
            continue
        witness = (str(kind), str(source), str(target))
        if witness in seen:
            raise ValueError(f"duplicate typed dependency edge: {witness}")
        seen.add(witness)
        # The source imports/depends on the target. These tuples retain that
        # orientation; message direction is assigned in the graph layer.
        result[str(kind)].append((index[str(source)], index[str(target)]))
    return result


def _masked_edge_batch(edges: dict[str, list[tuple[int, int]]], node_count: int,
                       *, seed: int, limit: int = 256):
    """Bounded directed examples; hide both orientations across all relations.

    Negatives mean absent from this observed graph, never semantically impossible.
    No quadratic complement matrix is materialized. Dense graphs may yield fewer
    samples; relations without sampled nonedges are omitted from the objective.
    """
    rng = random.Random(seed)
    observed = {pair for pairs in edges.values() for pair in pairs}
    examples = {}
    hidden = set()
    for kind, pairs in sorted(edges.items()):
        positives = rng.sample(sorted(pairs), min(limit, len(pairs)))
        negatives = set()
        for _ in range(max(1, len(positives)) * 32):
            if len(negatives) >= len(positives):
                break
            pair = (rng.randrange(node_count), rng.randrange(node_count))
            if pair[0] != pair[1] and pair not in observed:
                negatives.add(pair)
        if not negatives:
            continue
        positives = positives[:len(negatives)]
        examples[kind] = (positives, sorted(negatives))
        hidden.update(positives)
        hidden.update((b, a) for a, b in positives)
    visible = {kind: [pair for pair in pairs if pair not in hidden]
               for kind, pairs in edges.items()}
    return visible, examples


def _train_graph_encoder(
        refactoring_map: dict[str, Any], corpus: dict[str, Any],
        source_packet: dict[str, Any], *,
        hidden_dimension: int = 96, layers: int = 2, epochs: int = 80,
        learning_rate: float = 1e-3, mask_rate: float = 0.25,
        sce_alpha: float = 2.0,
        seed: int = 29, device: str = "auto", edge_ablation: bool = False,
        context_representation: str = "latent",
        edge_loss_weight: float = 0.0,
        ) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    try:
        import torch
        from torch import nn
    except ImportError as exc:  # pragma: no cover - environment-specific
        raise RuntimeError("graph-context training requires PyTorch") from exc

    train_rows, source_vectors, train_groups_digest = _validate_inputs(
        refactoring_map, corpus, source_packet,
    )
    if context_representation not in {"latent", "reconstruction"}:
        raise ValueError("context_representation must be latent or reconstruction")
    if (hidden_dimension < 8 or layers < 1 or epochs < 1
            or not math.isfinite(learning_rate) or learning_rate <= 0
            or not math.isfinite(mask_rate) or not 0 < mask_rate < 1
            or not math.isfinite(sce_alpha) or sce_alpha <= 0
            or not math.isfinite(edge_loss_weight) or edge_loss_weight < 0):
        raise ValueError("invalid graph-encoder dimensions or optimization parameters")
    if device == "auto":
        device = "cuda" if torch.cuda.is_available() else "cpu"
    if device.startswith("cuda") and not torch.cuda.is_available():
        raise ValueError("CUDA was requested but PyTorch reports no available device")

    train_ids = {row["artifactId"] for row in train_rows}
    all_nodes = sorted(source_vectors)
    train_nodes = sorted(train_ids)
    dimension = len(source_vectors[all_nodes[0]])
    if any(len(source_vectors[path]) != dimension for path in all_nodes):
        raise ValueError("source embedding dimensions differ")
    train_values = torch.tensor([source_vectors[path] for path in train_nodes],
                                dtype=torch.float32, device=device)
    mean = train_values.mean(dim=0)
    scale = train_values.std(dim=0, unbiased=False).clamp_min(1e-6)
    normalized_train = (train_values - mean) / scale

    train_edges = _edge_index(refactoring_map, train_nodes, induced=train_ids)
    degree = torch.zeros(len(train_nodes), dtype=torch.float32, device=device)
    edge_tensors: dict[str, tuple[Any, Any]] = {}
    for kind, pairs in train_edges.items():
        if not pairs:
            continue
        imports_from = torch.tensor([pair[0] for pair in pairs], dtype=torch.long, device=device)
        imports_to = torch.tensor([pair[1] for pair in pairs], dtype=torch.long, device=device)
        edge_tensors[kind] = (imports_from, imports_to)
        degree.index_add_(0, imports_from, torch.ones_like(imports_from, dtype=torch.float32))
        degree.index_add_(0, imports_to, torch.ones_like(imports_to, dtype=torch.float32))
    target_nodes = torch.nonzero(degree > 0, as_tuple=False).flatten()
    if target_nodes.numel() < 2 or not edge_tensors:
        raise ValueError("train-induced dependency graph needs at least two connected artifacts")

    class TypedDirectionalLayer(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            relation_ids = [f"{kind}__{direction}"
                            for kind in sorted(DEPENDENCY_KINDS)
                            for direction in ("dependency_to_dependent",
                                              "dependent_to_dependency")]
            self.relations = nn.ModuleDict({
                key: nn.Linear(hidden_dimension, hidden_dimension, bias=False)
                for key in relation_ids
            })
            self.update = nn.Sequential(
                nn.Linear(hidden_dimension * (len(relation_ids) + 1), hidden_dimension),
                nn.GELU(), nn.Linear(hidden_dimension, hidden_dimension),
            )
            self.norm = nn.LayerNorm(hidden_dimension)

        def forward(self, values: Any, edges: dict[str, tuple[Any, Any]]) -> Any:
            aggregate = []
            for kind in sorted(DEPENDENCY_KINDS):
                pair = edges.get(kind)
                for direction in ("dependency_to_dependent", "dependent_to_dependency"):
                    messages = torch.zeros_like(values)
                    counts = torch.zeros((values.shape[0], 1), dtype=values.dtype,
                                         device=values.device)
                    if pair is not None:
                        imports_from, imports_to = pair
                        if direction == "dependency_to_dependent":
                            message_source, message_target = imports_to, imports_from
                        else:
                            message_source, message_target = imports_from, imports_to
                        transformed = self.relations[f"{kind}__{direction}"](
                            values.index_select(0, message_source),
                        )
                        messages.index_add_(0, message_target, transformed)
                        counts.index_add_(
                            0, message_target,
                            torch.ones((len(message_target), 1), dtype=values.dtype,
                                       device=values.device),
                        )
                    aggregate.append(messages / counts.clamp_min(1.0))
            joined = torch.cat([values, *aggregate], dim=-1)
            return self.norm(values + self.update(joined))

    class GraphDenoiser(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.input = nn.Linear(dimension, hidden_dimension)
            self.layers = nn.ModuleList(TypedDirectionalLayer() for _ in range(layers))
            self.output = nn.Linear(hidden_dimension, dimension)
            self.edge_decoders = nn.ModuleDict({
                kind: nn.Bilinear(hidden_dimension, hidden_dimension, 1)
                for kind in sorted(DEPENDENCY_KINDS)
            }) if edge_loss_weight else nn.ModuleDict()

        def encode(self, values: Any, edges: dict[str, tuple[Any, Any]]) -> Any:
            hidden = self.input(values)
            for layer in self.layers:
                hidden = layer(hidden, edges)
            return hidden

        def decode(self, hidden: Any) -> Any:
            return self.output(hidden)

        def forward(self, values: Any, edges: dict[str, tuple[Any, Any]]) -> Any:
            return self.decode(self.encode(values, edges))

    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    generator = torch.Generator(device="cpu").manual_seed(seed)
    model = GraphDenoiser().to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=0.01)
    losses: list[float] = []
    edge_losses: list[float] = []
    edge_example_counts: list[int] = []
    for _epoch in range(epochs):
        model.train()
        order = target_nodes[torch.randperm(target_nodes.numel(), generator=generator)
                             .to(device)]
        masked_count = max(1, int(math.ceil(mask_rate * order.numel())))
        masked = order[:masked_count]
        corrupted = normalized_train.clone()
        corrupted[masked] = 0.0
        optimizer.zero_grad(set_to_none=True)
        prediction = model(corrupted, edge_tensors)
        predicted_targets = nn.functional.normalize(
            prediction.index_select(0, masked), dim=-1,
        )
        source_targets = nn.functional.normalize(
            normalized_train.index_select(0, masked), dim=-1,
        )
        cosine_error = (1.0 - (predicted_targets * source_targets).sum(dim=-1)).clamp_min(0.0)
        loss = cosine_error.pow(sce_alpha).mean()
        feature_loss = loss
        if edge_loss_weight:
            visible, examples = _masked_edge_batch(
                train_edges, len(train_nodes), seed=seed + 1000 + _epoch,
            )
            if not examples:
                raise ValueError("masked-edge objective needs sampled nonedges in the train graph")
            visible_tensors = {
                kind: tuple(torch.tensor(axis, dtype=torch.long, device=device)
                            for axis in zip(*pairs))
                for kind, pairs in visible.items() if pairs
            }
            # Separate encoding removes the target edges before any message
            # passing, including their reverse and other-relation aliases.
            edge_hidden = model.encode(corrupted, visible_tensors)
            logits, labels = [], []
            for kind, (positives, negatives) in examples.items():
                pairs = positives + negatives
                left = torch.tensor([a for a, _ in pairs], device=device)
                right = torch.tensor([b for _, b in pairs], device=device)
                logits.append(model.edge_decoders[kind](
                    edge_hidden[left], edge_hidden[right]).flatten())
                labels.extend([1.0] * len(positives) + [0.0] * len(negatives))
            edge_loss = nn.functional.binary_cross_entropy_with_logits(
                torch.cat(logits), torch.tensor(labels, device=device))
            loss = loss + edge_loss_weight * edge_loss
            edge_losses.append(float(edge_loss.detach().cpu()))
            edge_example_counts.append(len(labels))
        loss.backward()
        nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        optimizer.step()
        losses.append(float(feature_loss.detach().cpu()))

    full_edges_raw = _edge_index(refactoring_map, all_nodes)
    full_edges = {}
    full_degree = torch.zeros(len(all_nodes), dtype=torch.float32, device=device)
    for kind, pairs in full_edges_raw.items():
        if not pairs:
            continue
        imports_from = torch.tensor([pair[0] for pair in pairs], dtype=torch.long, device=device)
        imports_to = torch.tensor([pair[1] for pair in pairs], dtype=torch.long, device=device)
        full_edges[kind] = (imports_from, imports_to)
        full_degree.index_add_(0, imports_from, torch.ones_like(imports_from, dtype=torch.float32))
        full_degree.index_add_(0, imports_to, torch.ones_like(imports_to, dtype=torch.float32))

    full_values = torch.tensor([source_vectors[path] for path in all_nodes],
                               dtype=torch.float32, device=device)
    normalized_full = (full_values - mean) / scale
    context_targets = torch.nonzero(full_degree > 0, as_tuple=False).flatten()
    inference_mask_size = max(1, int(math.ceil(mask_rate * context_targets.numel())))
    inference_generator = torch.Generator(device="cpu").manual_seed(seed + 1)
    inference_order = context_targets[
        torch.randperm(context_targets.numel(), generator=inference_generator).to(device)
    ]
    context_vectors = torch.zeros_like(normalized_full)
    latent_vectors = torch.zeros((len(all_nodes), hidden_dimension), device=device)
    ablation_changes: list[dict[str, Any]] = []
    model.eval()
    with torch.no_grad():
        # Match the masked-node denoising objective at inference: each
        # connected artifact is predicted while its own source vector is
        # hidden. Disjoint batches cover all nodes in a deterministic number
        # of passes and prevent the residual path from copying the target.
        for start in range(0, inference_order.numel(), inference_mask_size):
            masked = inference_order[start:start + inference_mask_size]
            corrupted = normalized_full.clone()
            corrupted[masked] = 0.0
            encoded = model.encode(corrupted, full_edges)
            prediction = model.decode(encoded)
            latent_vectors[masked] = encoded[masked]
            context_vectors[masked] = prediction[masked]
            if edge_ablation:
                # Hold weights, source features, and target masks fixed;
                # remove only message-passing edges. This measures model
                # sensitivity, not a causal effect or classification quality.
                without_edges = model(corrupted, {})
                changes = (prediction[masked] - without_edges[masked]).square().mean(-1)
                ablation_changes.extend(
                    {"artifactId": all_nodes[index], "normalizedContextMSE": change}
                    for index, change in zip(masked.cpu().tolist(), changes.cpu().tolist())
                )
        graph_vectors = context_vectors * scale + mean
        # Zero in normalized coordinates would decode to the training mean.
        # Isolated artifacts instead receive an absent (zero) context block.
        graph_vectors[full_degree == 0] = 0.0
    split_by_artifact = {row["artifactId"]: row["split"] for row in corpus["rows"]}
    reconstruction_by_split: dict[str, dict[str, Any]] = {}
    with torch.no_grad():
        target_norms = normalized_full.norm(dim=-1)
        connected_flags = (full_degree > 0).cpu().tolist()
        nonzero_target_flags = (target_norms > 0).cpu().tolist()
        errors = (1.0 - (
            nn.functional.normalize(context_vectors, dim=-1)
            * nn.functional.normalize(normalized_full, dim=-1)
        ).sum(-1)).clamp_min(0.0).pow(sce_alpha)
        for split in ("train", "validation", "test", "unreviewed"):
            indices = [index for index, path in enumerate(all_nodes)
                       if split_by_artifact.get(path, "unreviewed") == split]
            connected = [index for index in indices if connected_flags[index]]
            evaluable = [index for index in connected if nonzero_target_flags[index]]
            reconstruction_by_split[split] = {
                "artifactCount": len(indices),
                "connectedArtifactCount": len(connected),
                "evaluatedArtifactCount": len(evaluable),
                "excludedZeroTargetNormCount": len(connected) - len(evaluable),
                "meanScaledCosineError": (
                    float(errors[evaluable].mean().cpu()) if evaluable else None
                ),
            }
    source_hashes = {
        row["artifactId"]: row["sourceSha256"] for row in source_packet["embeddings"]
    }
    exported_context = latent_vectors if context_representation == "latent" else graph_vectors
    combined = [
        {"artifactId": path,
         "sourceSha256": source_hashes[path],
         "vector": [*source_vectors[path], *exported_context[index].detach().cpu().tolist()]}
        for index, path in enumerate(all_nodes)
    ]
    base_training = source_packet["encoderTraining"]
    training = {
        **base_training,
        "method": MODEL_VERSION,
        "dataScope": "repository_train_split",
        "sourceSnapshotSha256": source_packet["sourceSnapshotSha256"],
        "trainingSplitGroupsSha256": train_groups_digest,
        "trainingArtifactIdsSha256": hashlib.sha256(
            "\0".join(train_nodes).encode("utf-8")).hexdigest(),
        "inputEncoderVersion": source_packet["encoderVersion"],
        "inputEncoderPacketSha256": source_packet["packetSha256"],
        "graphTrainingScope": "train_artifacts_and_train_induced_dependency_edges",
        "graphInferenceScope": "all_current_source_artifacts_and_typed_dependency_edges",
        "taxonomyLabelsUsedByObjective": False,
        "contextRepresentation": context_representation,
        "edgeLossWeight": edge_loss_weight,
    }
    packet = build_encoder_embedding_packet(
        refactoring_map, f"{source_packet['encoderVersion']}+{MODEL_VERSION}.{context_representation}",
        combined, encoder_training=training,
    )
    checkpoint = {
        "schema": "info_geometry.graph_context_encoder_checkpoint.v1",
        "modelVersion": MODEL_VERSION,
        "config": {"inputDimension": dimension, "hiddenDimension": hidden_dimension,
                   "layers": layers, "relationKinds": sorted(DEPENDENCY_KINDS),
                   "directions": ["dependency_to_dependent", "dependent_to_dependency"],
                   "objective": ("masked_source_features_and_directed_typed_edges"
                                 if edge_loss_weight else
                                 "masked_source_embedding_scaled_cosine_reconstruction"),
                   "contextRepresentation": context_representation,
                   "edgeLossWeight": edge_loss_weight,
                   "scaledCosineAlpha": sce_alpha},
        "normalization": {"mean": mean.detach().cpu().tolist(),
                          "scale": scale.detach().cpu().tolist()},
        "stateDict": {key: value.detach().cpu().tolist()
                      for key, value in model.state_dict().items()},
        "trainingProvenance": training,
    }
    report = {
        "schema": "info_geometry.graph_context_encoder_training_report.v1",
        "modelVersion": MODEL_VERSION,
        "sourceSnapshotSha256": packet["sourceSnapshotSha256"],
        "inputEncoderPacketSha256": source_packet["packetSha256"],
        "outputEmbeddingPacketSha256": packet["packetSha256"],
        "contextRepresentation": context_representation,
        "contextDimension": hidden_dimension if context_representation == "latent" else dimension,
        "trainingArtifactCount": len(train_nodes),
        "trainingConnectedArtifactCount": int(target_nodes.numel()),
        "trainingDependencyEdgeCount": sum(map(len, train_edges.values())),
        "fullInferenceArtifactCount": len(all_nodes),
        "fullInferenceDependencyEdgeCount": sum(map(len, full_edges_raw.values())),
        "inferenceMaskedArtifactCount": int(context_targets.numel()),
        "inferenceMaskBatchSize": inference_mask_size,
        "inferenceMaskPassCount": math.ceil(
            context_targets.numel() / inference_mask_size
        ),
        "trainingGroupDigest": train_groups_digest,
        "trainingObjective": ("masked_source_features_and_directed_typed_edges"
                              if edge_loss_weight else
                              "masked_source_embedding_scaled_cosine_reconstruction"),
        "scaledCosineAlpha": sce_alpha,
        "taxonomyLabelsUsedByObjective": False,
        "trainingScope": "train-induced graph only",
        "inferenceScope": "transductive over current source graph",
        "inferencePolicy": "deterministic_disjoint_masked_target_batches",
        "edgeAblation": {
            "enabled": edge_ablation,
            "method": "remove_all_inference_edges_with_fixed_weights_and_target_masks",
            "coordinateSystem": "train_standardized_embedding_coordinates",
            "artifactChanges": sorted(ablation_changes, key=lambda row: row["artifactId"]),
            "meanNormalizedContextMSE": (
                math.fsum(row["normalizedContextMSE"] for row in ablation_changes)
                / len(ablation_changes) if ablation_changes else None
            ),
            "authority": "model_sensitivity_not_causal_effect_or_taxonomy_accuracy",
        },
        "epochScaledCosineError": losses,
        "maskedEdgeReconstruction": {
            "enabled": edge_loss_weight > 0,
            "weight": edge_loss_weight,
            "epochBinaryCrossEntropy": edge_losses,
            "epochExampleCounts": edge_example_counts,
            "positiveLimitPerRelation": 256,
            "scope": "train-induced directed typed edges only",
            "maskPolicy": "remove_target_pair_both_orientations_all_relations",
            "negativeAuthority": "absent_observed_edge_not_semantic_impossibility",
            "evaluationAuthority": "training_loss_not_heldout_link_prediction_accuracy",
        },
        "reconstructionEvaluation": {
            "scope": "masked_target_transductive_current_graph",
            "metric": "scaled_cosine_error_in_train_standardized_coordinates",
            "bySplit": reconstruction_by_split,
            "authority": "feature_reconstruction_not_taxonomy_accuracy_or_inductive_generalization",
        },
        "device": str(device),
        "seed": seed,
        "authority": (
            "self-supervised graph-context representation; not taxonomy labels, "
            "causal importance, or semantic proof"
        ),
    }
    return packet, checkpoint, report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("reviewed_corpus_manifest", type=Path)
    parser.add_argument("source_embeddings", type=Path)
    parser.add_argument("--hidden-dimension", type=int, default=96)
    parser.add_argument("--layers", type=int, default=2)
    parser.add_argument("--epochs", type=int, default=80)
    parser.add_argument("--learning-rate", type=float, default=1e-3)
    parser.add_argument("--mask-rate", type=float, default=0.25)
    parser.add_argument("--sce-alpha", type=float, default=2.0)
    parser.add_argument("--edge-loss-weight", type=float, default=0.0,
                        help="Optional masked directed-edge reconstruction loss weight")
    parser.add_argument("--seed", type=int, default=29)
    parser.add_argument("--device", default="auto", help="auto, cpu, or cuda[:index]")
    parser.add_argument("--edge-ablation", action="store_true",
                        help="Measure fixed-model context sensitivity with inference edges removed")
    parser.add_argument("--context-representation", choices=("latent", "reconstruction"),
                        default="latent", help="Export encoder latents or decoded context features")
    parser.add_argument("--embeddings-out", type=Path, required=True)
    parser.add_argument("--checkpoint-out", type=Path, required=True)
    parser.add_argument("--report-out", type=Path, required=True)
    args = parser.parse_args()
    packet, checkpoint, report = _train_graph_encoder(
        _read_json(args.refactoring_map), _read_json(args.reviewed_corpus_manifest),
        _read_json(args.source_embeddings),
        hidden_dimension=args.hidden_dimension, layers=args.layers, epochs=args.epochs,
        learning_rate=args.learning_rate, mask_rate=args.mask_rate,
        sce_alpha=args.sce_alpha, seed=args.seed,
        device=args.device, edge_ablation=args.edge_ablation,
        context_representation=args.context_representation,
        edge_loss_weight=args.edge_loss_weight,
    )
    for path, payload in ((args.embeddings_out, packet),
                          (args.checkpoint_out, checkpoint), (args.report_out, report)):
        _write_json(path, payload)
    print(json.dumps({"embeddingPacketSha256": packet["packetSha256"],
                      "trainingArtifactCount": report["trainingArtifactCount"],
                      "inferenceArtifactCount": report["fullInferenceArtifactCount"],
                      "finalScaledCosineError": report["epochScaledCosineError"][-1],
                      "device": report["device"]},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
