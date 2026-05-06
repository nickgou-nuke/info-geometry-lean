from tools.infra.causal_chiral_prompt_builder import expr_context, weak_cone_bfs


def test_weak_cone_uses_dependency_and_reverse_edges() -> None:
    graph = {
        "a": {"dependencyComponentIds": ["b"], "reverseDependentComponentIds": ["c"]},
        "b": {"dependencyComponentIds": [], "reverseDependentComponentIds": ["a"]},
        "c": {"dependencyComponentIds": ["a"], "reverseDependentComponentIds": []},
    }

    assert weak_cone_bfs("a", graph) == {"a": 0, "b": 1, "c": 1}


def test_expr_context_is_honest_when_unavailable() -> None:
    context = expr_context("Missing.decl", {})

    assert context["available"] is False
    assert context["mode"] == "unavailable"


def test_expr_context_marks_fingerprint_as_diagnostic_proxy() -> None:
    context = expr_context(
        "Foo.bar",
        {
            "Foo.bar": {
                "feature_counts": {"binder_depth_proxy": 2},
                "feature_kind": {"kind_theorem": 1},
                "flags": {"has_doc": True},
                "provenance": {"method": "metadata_proxy_v1"},
                "level_0_decl_hash": "a",
                "level_1_local_hash": "b",
            }
        },
    )

    assert context["available"] is True
    assert context["mode"] == "metadata_fingerprint_proxy"
    assert "diagnostic only" in context["authority"]
