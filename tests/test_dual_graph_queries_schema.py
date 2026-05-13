from pathlib import Path


def test_dual_graph_queries_target_integrated_schema() -> None:
    text = Path("tools/infra/aql/dual_graph_queries.aql").read_text(encoding="utf-8")

    assert "ig_decl_nodes" not in text
    assert "ig_scc_nodes" not in text
    assert "e.predicate" not in text
    assert 'w.kind == "bvar_occurrence"' not in text
    assert 'w.kind == "binder_fiber_wire"' not in text

    assert "ig_decl_topologies" in text
    assert "ig_logic_vectors" in text
    assert "ig_translation_scc" in text
    assert "ig_kernel_equivalence_edges" in text
    assert "ig_triple_homomorphism_edges" in text
    assert "leanVerified" in text
    assert "safeForAutoRewrite" in text
    assert "triple_homomorphism_certificate" in text
    assert 'e.mode == "type"' in text
    assert "type-only mode must never be rewrite-safe" in text
    assert "finite incidence preserved, but theorem-level equivalence not certified" in text
    assert "MIN(grouped[*].hit.reviewOnly ? 1 : 0) == 1" in text
    assert 'w.wireLevel == "occurrence"' in text
    assert 'w.wireLevel == "fiber"' in text
