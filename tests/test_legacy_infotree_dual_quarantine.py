from tools.infra import legacy_infotree_dual_space, legacy_infotree_translation_sccs


def test_legacy_infotree_defaults_do_not_target_expr_graph_dual_namespace() -> None:
    assert legacy_infotree_dual_space.DEFAULT_INPUT_DIR == "artifacts/infotree/arango-lossless-dag-current"
    assert legacy_infotree_dual_space.DEFAULT_OUTPUT_DIR == "artifacts/infotree/legacy-dual"
    assert legacy_infotree_translation_sccs.DEFAULT_INPUT_DIR == "artifacts/infotree/legacy-dual"
    assert legacy_infotree_translation_sccs.DEFAULT_OUTPUT_DIR == "reports/dag/legacy-infotree-translation-sccs"


def test_legacy_infotree_translation_edges_are_not_lean_verified() -> None:
    fingerprints = [
        {
            "name": "A.foo",
            "kind": "theorem",
            "module": "A",
            "shapeHash": "sha256:shape",
            "translationHash": "sha256:translation",
        },
        {
            "name": "B.foo",
            "kind": "theorem",
            "module": "B",
            "shapeHash": "sha256:shape",
            "translationHash": "sha256:translation",
        },
    ]

    edges, sccs, _ = legacy_infotree_translation_sccs.build_translation_sccs(fingerprints, [], [])

    assert edges
    assert {edge["predicate"] for edge in edges} == {"derived_pattern_translation"}
    assert all(edge["leanVerified"] is False for edge in edges)
    assert all(edge["safeForAutoRewrite"] is False for edge in edges)
    assert any(len(scc["members"]) == 2 for scc in sccs)
