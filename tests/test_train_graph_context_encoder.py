"""Behavioral checks for provenance-bound graph-context exports."""
import math

import pytest

pytest.importorskip("torch")

from tests.test_train_taxonomy_baseline import _fixtures
from tools.repository_evolution.train_graph_context_encoder import (
    _masked_edge_batch, _train_graph_encoder,
)


@pytest.mark.parametrize("representation", ["latent", "reconstruction"])
def test_graph_training_preserves_sources_and_gives_isolates_no_context(representation):
    source_map, corpus, source_packet = _fixtures()
    source_map["dependencyEdges"] = [
        {"from": "src/Module0.lean", "to": "src/Module1.lean",
         "kind": "lean_source_import"},
        {"from": "src/Module1.lean", "to": "src/Module4.lean",
         "kind": "lean_source_import"},
    ]
    packet, checkpoint, report = _train_graph_encoder(
        source_map, corpus, source_packet, hidden_dimension=8,
        layers=1, epochs=1, device="cpu", edge_ablation=True,
        context_representation=representation,
    )
    assert any(value != 0 for value in checkpoint["normalization"]["mean"])
    originals = {row["artifactId"]: row for row in source_packet["embeddings"]}
    connected = {"src/Module0.lean", "src/Module1.lean", "src/Module4.lean"}
    for row in packet["embeddings"]:
        original = originals[row["artifactId"]]
        width = len(original["vector"])
        context_width = 8 if representation == "latent" else width
        assert len(row["vector"]) == width + context_width
        assert row["vector"][:width] == original["vector"]
        assert row["sourceSha256"] == original["sourceSha256"]
        assert all(math.isfinite(value) for value in row["vector"])
        if row["artifactId"] not in connected:
            assert row["vector"][width:] == [0.0] * context_width
    # The held-out boundary participates in inference, never training edges.
    assert report["trainingDependencyEdgeCount"] == 1
    assert report["fullInferenceDependencyEdgeCount"] == 2
    assert report["inferenceMaskedArtifactCount"] == 3
    assert report["taxonomyLabelsUsedByObjective"] is False
    evaluation = report["reconstructionEvaluation"]["bySplit"]
    assert evaluation["train"]["evaluatedArtifactCount"] == 2
    assert evaluation["validation"]["evaluatedArtifactCount"] == 1
    assert evaluation["test"]["evaluatedArtifactCount"] == 0
    assert evaluation["test"]["meanScaledCosineError"] is None
    assert evaluation["unreviewed"]["artifactCount"] == 0
    assert math.isfinite(evaluation["validation"]["meanScaledCosineError"])
    ablation = report["edgeAblation"]
    assert {row["artifactId"] for row in ablation["artifactChanges"]} == connected
    assert math.isfinite(ablation["meanNormalizedContextMSE"])
    assert ablation["meanNormalizedContextMSE"] > 0
    # Diagnostics must not change the exported representation or trained weights.
    baseline_packet, baseline_checkpoint, baseline_report = _train_graph_encoder(
        source_map, corpus, source_packet, hidden_dimension=8,
        layers=1, epochs=1, device="cpu", edge_ablation=False,
        context_representation=representation,
    )
    assert baseline_packet == packet
    assert baseline_checkpoint == checkpoint
    assert baseline_report["edgeAblation"]["artifactChanges"] == []


def test_heldout_edges_cannot_rescue_an_empty_training_graph():
    source_map, corpus, source_packet = _fixtures()
    source_map["dependencyEdges"] = [
        {"from": "src/Module0.lean", "to": "src/Module4.lean",
         "kind": "lean_source_import"},
    ]
    with pytest.raises(ValueError, match="train-induced dependency graph"):
        _train_graph_encoder(source_map, corpus, source_packet, epochs=1, device="cpu")


def test_edge_mask_removes_reverse_and_other_relation_shortcuts():
    edges = {"a": [(0, 1), (1, 2)], "b": [(1, 0), (0, 1)]}
    visible, examples = _masked_edge_batch(edges, 4, seed=9)
    assert (visible, examples) == _masked_edge_batch(edges, 4, seed=9)
    observed = {pair for pairs in edges.values() for pair in pairs}
    for positives, negatives in examples.values():
        assert len(positives) == len(negatives)
        assert not set(negatives) & observed
        assert all(a != b for a, b in negatives)
        for a, b in positives:
            for pairs in visible.values():
                assert (a, b) not in pairs
                assert (b, a) not in pairs


def test_dense_graph_does_not_invent_negative_edges():
    edges = {"a": [(a, b) for a in range(3) for b in range(3) if a != b]}
    visible, examples = _masked_edge_batch(edges, 3, seed=9)
    assert visible == edges
    assert examples == {}


def test_joint_feature_and_typed_edge_reconstruction_uses_train_graph_only():
    source_map, corpus, source_packet = _fixtures()
    source_map["dependencyEdges"] = [
        {"from": "src/Module0.lean", "to": "src/Module1.lean",
         "kind": "lean_source_import"},
        {"from": "src/Module1.lean", "to": "src/Module4.lean",
         "kind": "lean_source_import"},
    ]
    _, checkpoint, report = _train_graph_encoder(
        source_map, corpus, source_packet, hidden_dimension=8,
        layers=1, epochs=2, device="cpu", edge_loss_weight=0.2,
    )
    diagnostic = report["maskedEdgeReconstruction"]
    assert diagnostic["epochExampleCounts"] == [2, 2]
    assert all(math.isfinite(v) and v >= 0
               for v in diagnostic["epochBinaryCrossEntropy"])
    assert checkpoint["config"]["edgeLossWeight"] == 0.2
    assert any(key.startswith("edge_decoders.") for key in checkpoint["stateDict"])
    assert report["trainingDependencyEdgeCount"] == 1
