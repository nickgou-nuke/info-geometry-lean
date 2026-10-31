"""Provenance and mathematical-contract tests for attention-weighted SCCs."""
from __future__ import annotations

import math

import pytest

from tools.infra.graph_components import tarjan_scc
from tools.repository_evolution.attention_scc import (
    build_attention_scc_overlay,
    edge_reference,
)


def _fixture():
    edges = [
        {"from": "a", "to": "b", "kind": "python_import", "status": "observed"},
        {"from": "b", "to": "a", "kind": "python_import", "status": "observed"},
        {"from": "b", "to": "c", "kind": "python_import", "status": "observed"},
        {"from": "c", "to": "b", "kind": "python_import", "status": "observed"},
    ]
    graph = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "snapshot-1",
        },
        "files": [{"path": node} for node in ("a", "b", "c", "isolated")],
        "dependencyEdges": edges,
    }
    logits = {edge_reference(edge): 0.0 for edge in edges}
    logits[edge_reference(edges[2])] = math.log(3)
    packet = {
        "schema": "info_geometry.edge_attention_logits.v1",
        "sourceSnapshotSha256": "snapshot-1",
        "modelVersion": "test-model-v1",
        "featureVersion": "test-features-v1",
        "inverseTemperature": 1.0,
        "edges": [{"edgeRef": ref, "logit": logit} for ref, logit in logits.items()],
    }
    return graph, packet, edges


def test_iterative_tarjan_handles_deep_graphs_and_cycles():
    vertices = [f"v{i}" for i in range(2500)]
    adjacency = {vertices[i]: [vertices[i + 1]] for i in range(len(vertices) - 1)}
    adjacency[vertices[-1]] = [vertices[-2]]
    components = tarjan_scc(vertices, adjacency)
    assert components[0] == ["v0"]
    assert ["v2498", "v2499"] in components
    assert len(components) == 2499


def test_top_k_gibbs_support_changes_scc_and_retains_witness_factors():
    graph, packet, _ = _fixture()
    result = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})

    assert result["rawSccCount"] == 2  # {a,b,c} and isolated
    assert result["attentionSccCount"] == 3  # {a}, {b,c}, isolated
    assert result["selectedEdgeCount"] == 3
    b_factors = {row["to"]: row["probability"] for row in result["allEdgeFactors"]
                 if row["from"] == "b"}
    assert b_factors["c"] == pytest.approx(0.75)
    assert b_factors["a"] == pytest.approx(0.25)
    assert all(row["edgeRef"] for row in result["allEdgeFactors"] if row["selected"])
    assert result["status"] == "model_derived_navigation_candidate"


def test_source_gibbs_state_reports_entropy_and_omits_empty_distributions():
    graph, packet, _ = _fixture()
    result = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})

    states = {row["source"]: row for row in result["sourceAttentionStates"]}
    assert states["b"]["status"] == "normalized_finite_gibbs_state"
    assert states["b"]["outDegree"] == 2
    assert states["b"]["normalizationSum"] == pytest.approx(1.0)
    assert states["b"]["shannonEntropyNats"] == pytest.approx(
        -(0.25 * math.log(0.25) + 0.75 * math.log(0.75))
    )
    assert states["b"]["inverseSimpsonEffectiveSupport"] == pytest.approx(1.6)
    assert states["b"]["maxProbability"] == pytest.approx(0.75)
    assert states["a"]["normalizedEntropy"] == 0.0
    assert states["isolated"] == {
        "source": "isolated", "status": "no_outgoing_edges", "outDegree": 0,
    }


def test_source_gibbs_state_is_independent_of_scc_support_pruning():
    graph, packet, _ = _fixture()
    sparse = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})
    dense = build_attention_scc_overlay(
        graph, packet, {"kind": "minimum_probability", "threshold": 0.01}
    )
    assert sparse["sourceAttentionStates"] == dense["sourceAttentionStates"]


def test_full_positive_gibbs_support_preserves_raw_scc_partition():
    graph, packet, _ = _fixture()
    result = build_attention_scc_overlay(
        graph, packet, {"kind": "minimum_probability", "threshold": 0.01}
    )
    assert result["rawSccCount"] == result["attentionSccCount"] == 2
    assert result["selectedEdgeCount"] == result["observedDependencyEdgeCount"] == 4


def test_gibbs_normalization_is_stable_when_beta_times_logit_overflows():
    graph, packet, edges = _fixture()
    packet["inverseTemperature"] = 1e308
    logits = {row["edgeRef"]: row["logit"] for row in packet["edges"]}
    # This pair makes beta * logit overflow for the larger logit.  Centering
    # before scaling must still produce a valid finite distribution.
    logits[edge_reference(edges[2])] = 1e308
    logits[edge_reference(edges[1])] = -1e308
    packet["edges"] = [
        {"edgeRef": ref, "logit": logit} for ref, logit in logits.items()
    ]

    result = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})

    by_source = {}
    for factor in result["allEdgeFactors"]:
        assert math.isfinite(factor["probability"])
        by_source.setdefault(factor["from"], []).append(factor["probability"])
    for probabilities in by_source.values():
        assert sum(probabilities) == pytest.approx(1.0)


def test_top_k_uses_logits_when_small_gibbs_probabilities_underflow_together():
    edges = [
        {"from": "s", "to": "z_low", "kind": "python_import"},
        {"from": "s", "to": "a_mid", "kind": "python_import"},
        {"from": "s", "to": "top", "kind": "python_import"},
    ]
    graph = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "snapshot-underflow",
        },
        "files": [{"path": node} for node in ("s", "z_low", "a_mid", "top")],
        "dependencyEdges": edges,
    }
    logits = {
        edge_reference(edges[0]): -1e308,
        edge_reference(edges[1]): 0.0,
        edge_reference(edges[2]): 1e308,
    }
    packet = {
        "schema": "info_geometry.edge_attention_logits.v1",
        "sourceSnapshotSha256": "snapshot-underflow",
        "modelVersion": "test-model-v1",
        "featureVersion": "test-features-v1",
        "inverseTemperature": 1e308,
        "edges": [{"edgeRef": ref, "logit": value} for ref, value in logits.items()],
    }

    result = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 2})

    selected = {row["to"] for row in result["allEdgeFactors"] if row["selected"]}
    assert selected == {"a_mid", "top"}
    factors = {row["to"]: row for row in result["allEdgeFactors"]}
    assert factors["a_mid"]["probability"] == factors["z_low"]["probability"] == 0.0


def test_attention_scores_must_match_snapshot_and_cover_all_local_edges():
    graph, packet, _ = _fixture()
    stale = dict(packet, sourceSnapshotSha256="different-snapshot")
    with pytest.raises(ValueError, match="different source snapshot"):
        build_attention_scc_overlay(graph, stale, {"kind": "top_k", "k": 1})

    incomplete = dict(packet, edges=packet["edges"][:-1])
    with pytest.raises(ValueError, match="score every scoped local dependency edge"):
        build_attention_scc_overlay(graph, incomplete, {"kind": "top_k", "k": 1})


def test_attention_rejects_mixed_snapshot():
    graph, packet, _ = _fixture()
    graph["sourceSnapshot"]["worktreeConsistentDuringScan"] = False
    with pytest.raises(ValueError, match="not a consistent worktree snapshot"):
        build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})


def test_attention_can_score_a_single_typed_dependency_layer():
    graph, packet, _edges = _fixture()
    lean_edge = {"from": "a", "to": "c", "kind": "lean_source_import",
                 "status": "observed"}
    graph["dependencyEdges"].append(lean_edge)
    packet["edgeKinds"] = ["lean_source_import"]
    packet["edges"] = [{"edgeRef": edge_reference(lean_edge), "logit": 0.25}]

    result = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})

    assert result["edgeKinds"] == ["lean_source_import"]
    assert result["observedDependencyEdgeCount"] == 1
    assert result["selectedEdgeCount"] == 1


def test_attention_rejects_noncanonical_edge_kind_scope():
    graph, packet, _ = _fixture()
    packet["edgeKinds"] = ["python_import", "python_import"]
    with pytest.raises(ValueError, match="sorted unique"):
        build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 1})


def test_magnetic_flow_imbalance_archetypes_cluster_acyclic_dag_where_tarjan_collapses():
    # Pure acyclic DAG: cap_1, cap_2 -> bridge_1, bridge_2 -> own_1, own_2
    nodes = ("cap_1", "cap_2", "bridge_1", "bridge_2", "own_1", "own_2")
    edges = [
        {"from": "cap_1", "to": "bridge_1", "kind": "lean_source_import"},
        {"from": "cap_1", "to": "bridge_2", "kind": "lean_source_import"},
        {"from": "cap_2", "to": "bridge_1", "kind": "lean_source_import"},
        {"from": "cap_2", "to": "bridge_2", "kind": "lean_source_import"},
        {"from": "bridge_1", "to": "own_1", "kind": "lean_source_import"},
        {"from": "bridge_1", "to": "own_2", "kind": "lean_source_import"},
        {"from": "bridge_2", "to": "own_1", "kind": "lean_source_import"},
        {"from": "bridge_2", "to": "own_2", "kind": "lean_source_import"},
        {"from": "cap_1", "to": "own_1", "kind": "lean_source_import"},
    ]
    graph = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "snapshot-dag",
        },
        "files": [{"path": n} for n in nodes],
        "dependencyEdges": edges,
    }
    packet = {
        "schema": "info_geometry.edge_attention_logits.v1",
        "sourceSnapshotSha256": "snapshot-dag",
        "modelVersion": "test-model-v1",
        "featureVersion": "test-features-v1",
        "inverseTemperature": 2.0,
        "edgeKinds": ["lean_source_import"],
        "edges": [{"edgeRef": edge_reference(e), "logit": 1.0} for e in edges],
    }

    result = build_attention_scc_overlay(graph, packet, {"kind": "top_k", "k": 2})
    # Tarjan SCC collapses to 6 singleton components on any DAG
    assert result["rawSccCount"] == 6
    assert result["attentionSccCount"] == 6

    mag = result["magneticArchetypeTaxonomy"]
    assert mag["schema"] == "info_geometry.magnetic_flow_archetypes.v1"
    assert mag["hermitianResidualFrobenius"] == pytest.approx(0.0, abs=1e-12)
    # Magnetic flow-imbalance archetypes compress 6 DAG nodes into fewer role clusters
    assert mag["archetypeClusterCount"] < 6
    by_vertex = {row["vertex"]: row for row in mag["nodeMetrics"]}
    assert by_vertex["cap_1"]["flowImbalance"] == pytest.approx(1.0)
    assert by_vertex["own_1"]["flowImbalance"] == pytest.approx(-1.0)
    assert by_vertex["cap_1"]["archetypeRole"] == "capstone_source_archetype"
    assert by_vertex["own_1"]["archetypeRole"] == "owner_sink_archetype"
    assert len(mag["multiscaleRegimes"]) >= 3
