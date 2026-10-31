from __future__ import annotations

import numpy as np

from tools.infra.arango_magnetic_archetype_taxonomy import (
    SCHEMA,
    build_decl_graph_from_rows,
    build_multiscale_taxonomy,
    compute_directed_wl_hashes,
    compute_magnetic_laplacian_and_spectrum,
    compute_sinkhorn_gibbs_couplings,
    extract_micro_alleles,
)


def _synthetic_decl_dag() -> tuple[list[dict], list[dict]]:
    nodes = [
        {
            "_key": "owner_a",
            "_id": "decls/owner_a",
            "name": "InfoGeometry.Canonical.OwnerA",
            "module": "InfoGeometry.Canonical.Owner",
            "kind": "def",
            "dagShapeHash": "shape_owner_1",
            "canonicalTypeHash": "type_owner_1",
            "canonicalValueHash": "val_owner_1",
            "attrs": ["rep_depth:0:AlgebraicBase"],
            "decl": {
                "kind": "def",
                "typeFingerprint": {"nodeCount": 14, "appCount": 4, "forallCount": 2, "constCount": 5, "debruijnHistogram": [1, 2]},
                "valueFingerprint": {"nodeCount": 28, "appCount": 10, "lamCount": 3, "constCount": 7, "debruijnHistogram": [2, 3, 1]},
                "shapeHash": {"nodeCount": 32, "shapeHash": "shape_owner_1", "debruijnHistogram": [2, 3, 1]},
            },
        },
        {
            "_key": "owner_b",
            "_id": "decls/owner_b",
            "name": "InfoGeometry.Canonical.OwnerB",
            "module": "InfoGeometry.Canonical.Owner",
            "kind": "def",
            "dagShapeHash": "shape_owner_1",
            "canonicalTypeHash": "type_owner_1",
            "canonicalValueHash": "val_owner_2",
            "attrs": ["rep_depth:0:AlgebraicBase"],
            "decl": {
                "kind": "def",
                "typeFingerprint": {"nodeCount": 14, "appCount": 4, "forallCount": 2, "constCount": 5, "debruijnHistogram": [1, 2]},
                "valueFingerprint": {"nodeCount": 28, "appCount": 10, "lamCount": 3, "constCount": 7, "debruijnHistogram": [2, 3, 1]},
                "shapeHash": {"nodeCount": 32, "shapeHash": "shape_owner_1", "debruijnHistogram": [2, 3, 1]},
            },
        },
        {
            "_key": "bridge_a",
            "_id": "decls/bridge_a",
            "name": "InfoGeometry.Canonical.BridgeA",
            "module": "InfoGeometry.Canonical.Bridge",
            "kind": "theorem",
            "dagShapeHash": "shape_bridge_1",
            "canonicalTypeHash": "type_bridge_1",
            "canonicalValueHash": "val_bridge_1",
            "attrs": ["rep_depth:2:LieOperatorBridge"],
            "decl": {
                "kind": "theorem",
                "typeFingerprint": {"nodeCount": 24, "appCount": 9, "forallCount": 4, "constCount": 8, "debruijnHistogram": [3, 2, 1]},
                "valueFingerprint": {"nodeCount": 46, "appCount": 18, "lamCount": 5, "constCount": 12, "debruijnHistogram": [4, 3, 2]},
                "shapeHash": {"nodeCount": 54, "shapeHash": "shape_bridge_1", "debruijnHistogram": [4, 3, 2]},
            },
        },
        {
            "_key": "bridge_b",
            "_id": "decls/bridge_b",
            "name": "InfoGeometry.Canonical.BridgeB",
            "module": "InfoGeometry.Canonical.Bridge",
            "kind": "theorem",
            "dagShapeHash": "shape_bridge_1",
            "canonicalTypeHash": "type_bridge_1",
            "canonicalValueHash": "val_bridge_1",
            "attrs": ["rep_depth:2:LieOperatorBridge"],
            "decl": {
                "kind": "theorem",
                "typeFingerprint": {"nodeCount": 24, "appCount": 9, "forallCount": 4, "constCount": 8, "debruijnHistogram": [3, 2, 1]},
                "valueFingerprint": {"nodeCount": 46, "appCount": 18, "lamCount": 5, "constCount": 12, "debruijnHistogram": [4, 3, 2]},
                "shapeHash": {"nodeCount": 54, "shapeHash": "shape_bridge_1", "debruijnHistogram": [4, 3, 2]},
            },
        },
        {
            "_key": "capstone_a",
            "_id": "decls/capstone_a",
            "name": "InfoGeometry.Canonical.CapstoneA",
            "module": "InfoGeometry.Canonical.Capstone",
            "kind": "theorem",
            "dagShapeHash": "shape_cap_1",
            "canonicalTypeHash": "type_cap_1",
            "canonicalValueHash": "val_cap_1",
            "attrs": ["rep_depth:4:MasterSynthesis"],
            "decl": {
                "kind": "theorem",
                "typeFingerprint": {"nodeCount": 40, "appCount": 16, "forallCount": 6, "constCount": 14, "debruijnHistogram": [5, 4, 2, 1]},
                "valueFingerprint": {"nodeCount": 80, "appCount": 32, "lamCount": 8, "constCount": 20, "debruijnHistogram": [6, 5, 3, 1]},
                "shapeHash": {"nodeCount": 92, "shapeHash": "shape_cap_1", "debruijnHistogram": [6, 5, 3, 1]},
            },
        },
        {
            "_key": "capstone_b",
            "_id": "decls/capstone_b",
            "name": "InfoGeometry.Canonical.CapstoneB",
            "module": "InfoGeometry.Canonical.Capstone",
            "kind": "theorem",
            "dagShapeHash": "shape_cap_1",
            "canonicalTypeHash": "type_cap_2",
            "canonicalValueHash": "val_cap_2",
            "attrs": ["rep_depth:4:MasterSynthesis"],
            "decl": {
                "kind": "theorem",
                "typeFingerprint": {"nodeCount": 42, "appCount": 17, "forallCount": 6, "constCount": 15, "debruijnHistogram": [5, 4, 2, 1]},
                "valueFingerprint": {"nodeCount": 82, "appCount": 33, "lamCount": 8, "constCount": 21, "debruijnHistogram": [6, 5, 3, 1]},
                "shapeHash": {"nodeCount": 94, "shapeHash": "shape_cap_1", "debruijnHistogram": [6, 5, 3, 1]},
            },
        },
    ]
    # Pure DAG (zero directed cycles): capstone -> bridge -> owner
    edges = [
        {"_from": "decls/capstone_a", "_to": "decls/bridge_a", "kind": "value", "multiplicity": 2},
        {"_from": "decls/capstone_a", "_to": "decls/bridge_b", "kind": "value", "multiplicity": 2},
        {"_from": "decls/capstone_b", "_to": "decls/bridge_a", "kind": "type", "multiplicity": 1},
        {"_from": "decls/capstone_b", "_to": "decls/bridge_b", "kind": "type", "multiplicity": 1},
        {"_from": "decls/bridge_a", "_to": "decls/owner_a", "kind": "value", "multiplicity": 2},
        {"_from": "decls/bridge_a", "_to": "decls/owner_b", "kind": "type", "multiplicity": 1},
        {"_from": "decls/bridge_b", "_to": "decls/owner_a", "kind": "value", "multiplicity": 2},
        {"_from": "decls/bridge_b", "_to": "decls/owner_b", "kind": "type", "multiplicity": 1},
        # Shortcut edge to induce non-trivial magnetic loop frustration
        {"_from": "decls/capstone_a", "_to": "decls/owner_a", "kind": "value", "multiplicity": 1},
    ]
    return nodes, edges


def test_multiscale_magnetic_archetype_taxonomy_on_pure_dag() -> None:
    nodes, edges = _synthetic_decl_dag()
    graph = build_decl_graph_from_rows(nodes, edges)
    assert len(graph.nodes) == 6
    assert len(graph.edges) == 9
    assert graph.dna_matrix.shape == (6, 18)

    wl_hashes = compute_directed_wl_hashes(graph, rounds=2)
    alleles = extract_micro_alleles(graph, wl_hashes, min_cluster_size=2)
    # bridge_a and bridge_b have identical WL + shape + type + value fingerprints
    assert len(alleles) >= 1
    assert any(a["allele_class"] == "exact_type_and_value_clone" for a in alleles)

    p_mat, edge_meta = compute_sinkhorn_gibbs_couplings(graph, beta=2.0)
    assert p_mat.shape == (6, 6)
    assert len(edge_meta) == 9

    mag = compute_magnetic_laplacian_and_spectrum(p_mat, q_charge=0.25, n_eigen=4)
    assert mag["hermitian_residual"] < 1e-12
    assert len(mag["eigenvalues"]) >= 2
    # Shortcut edge capstone_a -> owner_a creates magnetic frustration across the triangle
    assert mag["total_frustration"] > 0.0
    # Capstones only have outgoing edges (+1 imbalance); owners only have incoming edges (-1 imbalance)
    cap_idx = graph.node_index["InfoGeometry.Canonical.CapstoneA"]
    own_idx = graph.node_index["InfoGeometry.Canonical.OwnerA"]
    assert np.isclose(mag["flow_imbalance"][cap_idx], 1.0)
    assert np.isclose(mag["flow_imbalance"][own_idx], -1.0)

    taxonomy = build_multiscale_taxonomy(
        graph,
        beta_meso=2.0,
        beta_macro=0.5,
        q_charge=0.25,
        n_meso_clusters=3,
        n_macro_phyla=2,
        run_id="unit_test",
    )
    assert taxonomy["schema"] == SCHEMA
    assert taxonomy["scales"]["L_meso_species"]["species_count"] == 3
    roles = set(taxonomy["scales"]["L_meso_species"]["role_distribution"].keys())
    assert "owner_source_species" in roles or "capstone_sink_species" in roles
    assert taxonomy["balaban_schur_coarse_graining"]["computed"] is True
    assert taxonomy["balaban_schur_coarse_graining"]["schur_pos_def_verified"] is True
