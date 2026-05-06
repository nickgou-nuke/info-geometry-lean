from tools.infra.ingest_semantic_content_audit import build_rows, graph_context, priority_for, status_allowed


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


def test_graph_context_prefers_enclosing_declaration_when_known() -> None:
    graph = {
        "nodes_by_name": {
            "M.a": {"module": "M"},
            "M.b": {"module": "M"},
            "N.use": {"module": "N"},
        },
        "decls_by_module": {"M": ["M.a", "M.b"], "N": ["N.use"]},
        "reverse_dependents": {"M.a": {"N.use"}, "M.b": set()},
    }

    ctx = graph_context({"module": "M"}, graph, enclosing_decl="M.a")

    assert ctx["candidate_decl_sample"] == ["M.a"]
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
                        "enclosing_decl": "M.t",
                        "enclosing_decl_kind": "theorem",
                        "enclosing_decl_line": 3,
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
    assert rows["hive_tasks"][0]["task_family"] == "semantic_content_repair"
    assert rows["hive_tasks"][0]["enclosing_decl"]["decl"] == "M.t"
    assert rows["hive_tasks"][0]["category"] == "trivial-theorem"
    assert rows["hive_tasks"][0]["direct_importer_count"] == 0
    assert rows["hive_tasks"][0]["forbidden_importer_count"] == 0
    assert rows["hive_tasks"][0]["authority"] == "source_diagnostic_not_proof"


def test_min_status_filters_less_severe_hive_tasks() -> None:
    assert status_allowed("quarantine_manifest_inconsistency", "vacuous_or_surrogate_surface")
    assert status_allowed("proof_hole_blocker", "vacuous_or_surrogate_surface")
    assert status_allowed("vacuous_or_surrogate_surface", "vacuous_or_surrogate_surface")
    assert not status_allowed("review_scaffold_surface", "vacuous_or_surrogate_surface")


def test_finding_and_task_keys_are_idempotent_across_runs() -> None:
    report = {
        "schema": "info_geometry.semantic_content_audit.v1",
        "summary": {"finding_count": 1},
        "modules": [
            {
                "module": "M",
                "path": "lean/M.lean",
                "semantic_status": "proof_hole_blocker",
                "recommended_action": "repair",
                "finding_categories": ["proof-hole"],
                "direct_importer_count": 1,
                "forbidden_importer_count": 1,
                "importer_class_counts": {},
                "direct_importers": [],
                "source_excerpts": [{"line": 4, "text": "4:   sorry"}],
                "findings": [
                    {
                        "path": "lean/M.lean",
                        "line": 4,
                        "category": "proof-hole",
                        "detail": "sorry/admit placeholder",
                        "enclosing_decl": "M.t",
                        "enclosing_decl_kind": "theorem",
                        "enclosing_decl_line": 3,
                    }
                ],
            }
        ],
    }
    graph = {"nodes_by_name": {}, "decls_by_module": {}, "reverse_dependents": {}}

    rows_a = build_rows(report, graph, run_key="run_a", min_status="vacuous_or_surrogate_surface")
    rows_b = build_rows(report, graph, run_key="run_b", min_status="vacuous_or_surrogate_surface")

    assert rows_a["semantic_content_audit_findings"][0]["_key"] == rows_b["semantic_content_audit_findings"][0]["_key"]
    assert rows_a["hive_tasks"][0]["_key"] == rows_b["hive_tasks"][0]["_key"]
