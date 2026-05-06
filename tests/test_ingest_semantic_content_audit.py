from tools.infra.ingest_semantic_content_audit import build_rows, graph_context, priority_for


def test_graph_context_uses_local_reverse_dependency_edges() -> None:
    graph = {
        "nodes_by_name": {
            "M.a": {"module": "M"},
            "M.b": {"module": "M"},
            "N.use": {"module": "N"},
        },
        "decls_by_module": {"M": ["M.a", "M.b"], "N": ["N.use"]},
        "reverse_dependents": {"M.a": {"N.use"}, "M.b": set()},
    }

    ctx = graph_context({"module": "M"}, graph)

    assert ctx["candidate_decl_count"] == 2
    assert ctx["graph_reverse_dependent_count"] == 1


def test_priority_combines_severity_importers_and_reverse_impact() -> None:
    module = {
        "semantic_status": "proof_hole_blocker",
        "direct_importer_count": 2,
        "forbidden_importer_count": 1,
    }
    ctx = {"graph_reverse_dependent_count": 4}

    assert priority_for(module, ctx) == 110.0


def test_build_rows_creates_findings_and_repair_tasks() -> None:
    report = {
        "schema": "info_geometry.semantic_content_audit.v1",
        "summary": {"finding_count": 1},
        "modules": [
            {
                "module": "M",
                "path": "lean/M.lean",
                "semantic_status": "vacuous_or_surrogate_surface",
                "recommended_action": "rewrite",
                "finding_categories": ["trivial-theorem"],
                "direct_importer_count": 0,
                "forbidden_importer_count": 0,
                "importer_class_counts": {},
                "direct_importers": [],
                "source_excerpts": [{"line": 3, "text": "3: theorem t : True := by trivial"}],
                "findings": [
                    {
                        "path": "lean/M.lean",
                        "line": 3,
                        "category": "trivial-theorem",
                        "detail": "theorem/lemma proven by trivial",
                    }
                ],
            }
        ],
    }
    graph = {"nodes_by_name": {}, "decls_by_module": {}, "reverse_dependents": {}}

    rows = build_rows(report, graph, run_key="r")

    assert len(rows["semantic_content_audit_modules"]) == 1
    assert len(rows["semantic_content_audit_findings"]) == 1
    assert rows["hive_tasks"][0]["task_kind"] == "constructivity.repair.vacuous"
