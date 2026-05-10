from __future__ import annotations

import networkx as nx

from tools.alexandria.graph_context_rank import activated_edges, build_graph, coarse_components, query_abstraction_score, scc_quotient_scores, tokenize


def test_conductive_debruijn_edges_gain_query_aligned_weight() -> None:
    chunks = [
        {"_key": "chunk_a", "tokens": ["krein", "projection"]},
        {"_key": "chunk_b", "tokens": ["j", "self", "adjoint"]},
        {"_key": "chunk_c", "tokens": ["banach", "space"]},
    ]
    debruijn_edges = [
        {
            "_from": "alexandria_chunks/chunk_a",
            "_to": "alexandria_chunks/chunk_b",
            "transition_probability": 0.45,
            "overlap_symbols": ["Krein space", "projection"],
            "direction": "semantic_sequence_overlap",
        },
        {
            "_from": "alexandria_chunks/chunk_a",
            "_to": "alexandria_chunks/chunk_c",
            "transition_probability": 0.45,
            "overlap_symbols": ["Banach space"],
            "direction": "semantic_sequence_overlap",
        },
    ]

    graph = build_graph(
        nx,
        chunks,
        [],
        [],
        [],
        debruijn_edges,
        [],
        query_tokens=tokenize("Krein projection"),
        conductive=True,
    )

    assert graph["chunk_a"]["chunk_b"]["kind"] == "debruijn_sequence"
    assert graph["chunk_a"]["chunk_b"]["conductivity"] > graph["chunk_a"]["chunk_c"]["conductivity"]
    assert graph["chunk_a"]["chunk_b"]["weight"] > graph["chunk_a"]["chunk_c"]["weight"]
    active = activated_edges(graph, {chunk["_key"]: chunk for chunk in chunks}, limit=1)
    assert active[0]["to"] == "chunk_b"
    assert active[0]["overlap_symbols"] == ["Krein space", "projection"]


def test_coarse_components_group_connected_context_by_entities() -> None:
    chunks = [
        {"_key": "chunk_a", "tokens": ["krein", "operator"], "chunkKind": "definition", "text": "Definition. Krein operator."},
        {"_key": "chunk_b", "tokens": ["krein", "projection"], "chunkKind": "theorem", "text": "Theorem. Krein projection."},
    ]
    graph = build_graph(
        nx,
        chunks,
        [{"_key": "ent_krein", "normalized": "Krein space", "entityType": "concept", "confidence": 1.0}],
        [
            {"_from": "alexandria_chunks/chunk_a", "_to": "alexandria_entities/ent_krein"},
            {"_from": "alexandria_chunks/chunk_b", "_to": "alexandria_entities/ent_krein"},
        ],
        [],
        [],
        [],
        query_tokens=tokenize("Krein operator theory"),
        conductive=True,
    )
    entities_for_chunk = {
        "chunk_a": [{"normalized": "Krein space"}],
        "chunk_b": [{"normalized": "Krein space"}],
    }
    components = coarse_components(
        nx,
        graph,
        chunks,
        entities_for_chunk,
        {"chunk_a": 0.3, "chunk_b": 0.4},
        tokenize("Krein operator theory"),
    )

    assert query_abstraction_score(tokenize("Krein operator theory")) >= 0.5
    assert components[0]["memberCount"] == 2
    assert "Krein space" in components[0]["representativeTerms"]


def test_scc_quotient_scores_distribute_component_score_to_cycle_members() -> None:
    graph = nx.DiGraph()
    graph.add_edge("a", "b", weight=1.0)
    graph.add_edge("b", "a", weight=1.0)
    graph.add_edge("b", "c", weight=0.5)

    scores, quotient = scc_quotient_scores(nx, graph, {"a": 1.0})

    cycle = next(row for row in quotient if set(row["members"]) == {"a", "b"})
    assert cycle["internalCycle"] is True
    assert scores["a"] == scores["b"]
    assert scores["a"] > 0
