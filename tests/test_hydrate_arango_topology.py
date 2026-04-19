import json
from pathlib import Path

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
    assert len(member_edges) == 3
    assert len(quotient_edges) == 1

    member_a = next(row for row in member_edges if row["member_key"] == "a")
    assert member_a["_from"] == f"{RAW_NODE_COLLECTION}/a"
    assert member_a["_to"].startswith("topology_overlay/scc_")
    assert member_a["attrs"]["direction"] == "raw_to_scc"

    quotient = quotient_edges[0]
    assert quotient["kind"] == "quotient"
    assert quotient["attrs"]["witness_count"] == 1
    assert quotient["witness_raw_edge_keys"] == ["e2"]
