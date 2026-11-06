import json
from copy import deepcopy
from pathlib import Path

import pytest

from tools.infra.hydrate_arango_topology import hydrate


RAW_NODE_COLLECTION = "raw_infotree_nodes"


def test_hydrate_preserves_raw_edges_and_adds_layered_scc_overlay() -> None:
    nodes = [
        {"_key": "a", "id": "raw/a", "kind": "expr", "graphKind": "expr", "attrs": {}},
        {"_key": "b", "id": "raw/b", "kind": "expr", "graphKind": "expr", "attrs": {}},
        {"_key": "c", "id": "raw/c", "kind": "expr", "graphKind": "expr", "attrs": {}},
    ]
    edges = [
        {"_key": "e0", "_from": f"{RAW_NODE_COLLECTION}/a", "_to": f"{RAW_NODE_COLLECTION}/b", "kind": "ast", "role": "fn"},
        {"_key": "e1", "_from": f"{RAW_NODE_COLLECTION}/b", "_to": f"{RAW_NODE_COLLECTION}/a", "kind": "ast", "role": "arg"},
        {"_key": "e2", "_from": f"{RAW_NODE_COLLECTION}/b", "_to": f"{RAW_NODE_COLLECTION}/c", "kind": "ast", "role": "body"},
    ]

    result = hydrate(
        nodes,
        edges,
        raw_layer_policy="LOSSLESS",
        raw_node_collection=RAW_NODE_COLLECTION,
        topology_overlay_collection="topology_overlay",
    )

    assert len(result["nodes"]) == len(nodes)
    assert len(result["edges"]) == len(edges)
    assert result["metadata"]["raw_nodes_preserved"] is True
    assert result["metadata"]["raw_edges_preserved"] is True

    raw_a = next(row for row in result["nodes"] if row["_key"] == "a")
    assert "layer:raw" in raw_a["labels"]
    assert raw_a["attrs"]["layer"] == "raw"
    assert raw_a["attrs"]["grain"] == "fine"
    assert raw_a["attrs"]["overlay_model"] == "layered_tensor_network"

    raw_edge = next(row for row in result["edges"] if row["_key"] == "e0")
    assert raw_edge["attrs"]["preserved_one_for_one"] is True
    assert "layer:raw" in raw_edge["labels"]

    overlay_nodes = result["overlay_nodes"]
    overlay_edges = result["overlay_edges"]
    assert len(overlay_nodes) == 2  # SCC {a,b} and singleton {c}

    scc_big = next(row for row in overlay_nodes if row["scc_size"] == 2)
    assert scc_big["layer"] == "topology_overlay"
    assert scc_big["grain"] == "scc"
    assert "topology:preserving_overlay" in scc_big["labels"]

    member_edges = [row for row in overlay_edges if row["role"] == "member_of_scc"]
    quotient_edges = [row for row in overlay_edges if row["role"] == "scc_quotient"]
    internal_edges = [row for row in overlay_edges if row["role"] == "scc_internal"]
    assert len(member_edges) == 3
    assert len(quotient_edges) == 1
    assert len(internal_edges) == 1

    member_a = next(row for row in member_edges if row["member_key"] == "a")
    assert member_a["_from"] == f"{RAW_NODE_COLLECTION}/a"
    assert member_a["_to"].startswith("topology_overlay/scc_")
    assert member_a["attrs"]["direction"] == "raw_to_scc"

    quotient_by_witnesses = {
        tuple(row["witness_raw_edge_keys"]): row
        for row in quotient_edges + internal_edges
    }
    internal_witness = quotient_by_witnesses[("e0", "e1")]
    assert internal_witness["role"] == "scc_internal"
    assert internal_witness["kind"] == "ast"
    assert internal_witness["multiplicity"] == 2
    assert internal_witness["src_scc"] == internal_witness["dst_scc"]
    assert internal_witness["attrs"]["witness_count"] == 2

    quotient = quotient_by_witnesses[("e2",)]
    assert quotient["kind"] == "ast"
    assert quotient["multiplicity"] == 1
    assert quotient["attrs"]["witness_count"] == 1


def test_persisted_vertex_keys_drive_resolution_and_round_trip_through_importer(tmp_path: Path) -> None:
    from tools.infra.arango_layered_ingest import CollectionSpec, iter_jsonl

    nodes = [
        {"_key": "InfoGeometry.a", "key": "secondary metadata", "name": "InfoGeometry.a", "attrs": ["original"]},
        {"_key": "custom_b", "name": "InfoGeometry.b", "attrs": {"original": {"x": 1}}},
        {"_key": "custom_c", "name": "InfoGeometry.c"},
    ]
    edges = [
        {
            "_key": "e_ab",
            "src": "InfoGeometry.a",
            "dst": "InfoGeometry.b",
            "kind": "value",
            "attrs": ["edge-original"],
        },
        {"_key": "e_ba", "src": "InfoGeometry.b", "dst": "InfoGeometry.a", "kind": "value"},
        {"_key": "e_bc", "src": "InfoGeometry.b", "dst": "InfoGeometry.c", "kind": "value"},
    ]
    original = deepcopy((nodes, edges))
    result = hydrate(
        nodes,
        edges,
        raw_layer_policy="LOSSLESS",
        raw_node_collection="custom_source_nodes",
        topology_overlay_collection="custom_overlay",
    )

    assert (nodes, edges) == original
    assert result["metadata"]["edge_loss_count"] == 0
    assert result["nodes"][0]["_key"] == "InfoGeometry.a"
    assert "original" in result["nodes"][0]["attrs"]
    assert result["nodes"][1]["attrs"]["original"] == {"x": 1}
    assert "edge-original" in result["edges"][0]["attrs"]
    assert result["edges"][0]["_from"] == "custom_source_nodes/InfoGeometry.a"
    assert result["edges"][0]["_to"] == "custom_source_nodes/custom_b"
    assert result["edges"][0]["endpoint_keys_resolved"] is True
    member_edges = [edge for edge in result["overlay_edges"] if edge["role"] == "member_of_scc"]
    assert all(edge["_to"].startswith("custom_overlay/") for edge in member_edges)

    node_path = tmp_path / "nodes.jsonl"
    edge_path = tmp_path / "edges.jsonl"
    node_path.write_text("".join(json.dumps(row) + "\n" for row in result["nodes"]))
    edge_path.write_text("".join(json.dumps(row) + "\n" for row in result["edges"]))
    imported_nodes = list(iter_jsonl(node_path, CollectionSpec("selected_nodes", node_path, False)))
    imported_edges = list(
        iter_jsonl(
            edge_path,
            CollectionSpec(
                "edges",
                edge_path,
                True,
                vertex_collection="selected_nodes",
                source_vertex_collection="custom_source_nodes",
            ),
        )
    )
    identifiers = {"selected_nodes/" + row["_key"] for row in imported_nodes}
    assert all(row["_from"] in identifiers and row["_to"] in identifiers for row in imported_edges)
    assert imported_edges[0]["src"] == "InfoGeometry.a"

    overlay_path = tmp_path / "overlay_edges.jsonl"
    overlay_path.write_text("".join(json.dumps(row) + "\n" for row in result["overlay_edges"]))
    overlay_nodes_path = tmp_path / "overlay_nodes.jsonl"
    overlay_nodes_path.write_text(
        "".join(json.dumps(row) + "\n" for row in result["overlay_nodes"])
    )
    imported_overlay_nodes = list(
        iter_jsonl(
            overlay_nodes_path,
            CollectionSpec("target_overlay_nodes", overlay_nodes_path, False),
        )
    )
    imported_overlay_edges = list(
        iter_jsonl(
            overlay_path,
            CollectionSpec(
                "target_overlay_edges",
                overlay_path,
                True,
                vertex_collection="selected_nodes",
                overlay_collection="target_overlay_nodes",
                source_vertex_collection="custom_source_nodes",
                source_overlay_collection="custom_overlay",
            ),
        )
    )
    imported_member_edges = [
        edge for edge in imported_overlay_edges if edge["role"] == "member_of_scc"
    ]
    assert imported_member_edges
    imported_overlay_ids = {
        "target_overlay_nodes/" + row["_key"] for row in imported_overlay_nodes
    }
    assert all(
        edge["_from"] in identifiers and edge["_to"] in imported_overlay_ids
        for edge in imported_member_edges
    )
    assert all(edge["endpoint_keys_resolved"] is True for edge in imported_member_edges)
    for edge in imported_overlay_edges:
        if edge["role"] in {"scc_internal", "scc_quotient"}:
            assert edge["_from"] in imported_overlay_ids
            assert edge["_to"] in imported_overlay_ids
    assert any(edge["role"] == "scc_internal" for edge in imported_overlay_edges)
    assert any(edge["role"] == "scc_quotient" for edge in imported_overlay_edges)


def test_self_loop_is_cyclic_and_internal_witness_is_not_a_quotient_arc() -> None:
    nodes = [{"_key": "a"}, {"_key": "b"}]
    edges = [
        {"_key": "loop", "_from": f"{RAW_NODE_COLLECTION}/a", "_to": f"{RAW_NODE_COLLECTION}/a"},
        {"_key": "ab", "_from": f"{RAW_NODE_COLLECTION}/a", "_to": f"{RAW_NODE_COLLECTION}/b"},
    ]
    result = hydrate(
        nodes,
        edges,
        raw_layer_policy="LOSSLESS",
        raw_node_collection=RAW_NODE_COLLECTION,
        topology_overlay_collection="topology_overlay",
    )

    assert "topology:cyclic" in result["nodes"][0]["labels"]
    quotient = [edge for edge in result["overlay_edges"] if edge["role"] == "scc_quotient"]
    internal = [edge for edge in result["overlay_edges"] if edge["role"] == "scc_internal"]
    assert len(quotient) == 1
    assert quotient[0]["witness_raw_edge_keys"] == ["ab"]
    assert len(internal) == 1
    assert internal[0]["witness_raw_edge_keys"] == ["loop"]


def test_ambiguous_aliases_and_foreign_addressed_endpoints_are_rejected() -> None:
    with pytest.raises(ValueError, match="ambiguous vertex alias"):
        hydrate(
            [{"_key": "a", "name": "same"}, {"_key": "b", "name": "same"}],
            [],
            raw_layer_policy="LOSSLESS",
            raw_node_collection=RAW_NODE_COLLECTION,
            topology_overlay_collection="topology_overlay",
        )

    with pytest.raises(ValueError, match="outside selected vertex collection"):
        hydrate(
            [{"_key": "a"}],
            [{"_from": "foreign/a", "_to": f"{RAW_NODE_COLLECTION}/a"}],
            raw_layer_policy="LOSSLESS",
            raw_node_collection=RAW_NODE_COLLECTION,
            topology_overlay_collection="topology_overlay",
        )


def test_descent_verifier_selects_internal_evidence_for_same_scc() -> None:
    from tools.infra.verify_layered_arango_descent import scc_witness_role

    assert scc_witness_role(4, 4) == "scc_internal"
    assert scc_witness_role(4, 5) == "scc_quotient"


def test_legacy_name_form_raw_endpoint_still_maps_to_hashed_key() -> None:
    from tools.infra.arango_layered_ingest import dag_decl_key, rewrite_endpoint

    rewritten = rewrite_endpoint(
        "ig_nodes/InfoGeometry.legacy",
        raw_collection="selected_nodes",
        overlay_collection=None,
        row={"src": "InfoGeometry.other"},
    )
    assert rewritten == f"selected_nodes/{dag_decl_key('InfoGeometry.legacy')}"
