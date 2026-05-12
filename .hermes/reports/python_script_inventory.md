# Live Python script inventory

Scope: live working tree Python files, excluding dependency/build/cache/vendor trees: .git, .lake, .venv*, __pycache__, .pytest_cache, external, external_refs, infogeometry.egg-info.

Total Python files analysed: 672

Counts by top-level group:

- archive: 15
- cli: 2
- jsonschema: 3
- jsonschema_shadow: 3
- lean: 1
- leantrail: 12
- presentation: 1
- scratch: 1
- scripts: 19
- skills: 1
- src: 28
- tests: 226
- tools: 360


## archive

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `.scripts_archive/bulk_namespace_rewrite.py` | 173 | yes | Archived/legacy script for bulk namespace rewrite; not a live authority surface unless revived. |
| `.scripts_archive/gather_cluster_code.py` | 49 | yes | Archived/legacy script for gather cluster code; not a live authority surface unless revived. |
| `.scripts_archive/namespace_patch_plan.py` | 68 | yes | Archived/legacy script for namespace patch plan; not a live authority surface unless revived. |
| `archive/legacy/scripts/agent_doc_gen.py` | 71 | yes | LEGACY compatibility generator for local declaration-neighborhood LaTeX stubs. This script still depends on `tools.graph` and the older graph wrapper lane. Prefer the authoritat... |
| `archive/legacy/scripts/auto_tag.py` | 276 | yes | LEGACY bulk blueprint tag generator from `docs-map/declarations.json`. The supported current workflow is `tools/infra/refresh_blueprint_tags.py`, which uses the public declarati... |
| `archive/legacy/scripts/autonomous_researcher.py` | 408 | yes | Archived/legacy script for autonomous researcher; not a live authority surface unless revived. |
| `archive/legacy/scripts/build_theory_manifest.py` | 181 | yes | Archived/legacy script for build theory manifest; not a live authority surface unless revived. |
| `archive/legacy/scripts/cluster_theory.py` | 121 | yes | Archived/legacy script for cluster theory; not a live authority surface unless revived. |
| `archive/legacy/scripts/generate_library_index.py` | 116 | yes | LEGACY compatibility generator for the exhaustive LaTeX library index. This script still depends on `tools.graph` and the older graph wrapper surface. Prefer the dedicated `Info... |
| `archive/legacy/scripts/graph.py` | 227 | yes | Legacy/compatibility graph consumer for older InfoGeometry declaration exports. Do not treat this module as the canonical causal-order source of truth. The current authoritative... |
| `archive/legacy/scripts/graph_to_blueprint_bulk.py` | 303 | yes | LEGACY graph-only generator for bulk `[blueprint]` tags. This script reads `docs-map/graph.json` from the older declaration-graph lane. The supported current workflow is `tools/... |
| `archive/legacy/scripts/graph_to_blueprint_inplace.py` | 376 | yes | LEGACY bootstrap tool for annotating Lean source with `@[blueprint]` tags from `docs-map/graph.json`. This script belongs to the older graph-only blueprint lane. The supported c... |
| `archive/legacy/scripts/make_graph.py` | 314 | yes | Archived/legacy script for make graph; not a live authority surface unless revived. |
| `archive/legacy/scripts/refactor_plan.py` | 365 | yes | Archived/legacy script for refactor plan; not a live authority surface unless revived. |
| `archive/legacy/scripts/skynet.py` | 131 | yes | Archived/legacy script for skynet; not a live authority surface unless revived. |

## cli

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `cli/__init__.py` | 2 |  | Command entrypoints for local InfoGeometry tooling. |
| `cli/igf.py` | 18 | yes | Compatibility wrapper for the package-local igf CLI. |

## jsonschema

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `jsonschema/__init__.py` | 224 |  | Package initializer for jsonschema; defines/reexports Draft202012Validator, FormatChecker, RefResolver, _looks_like_ref, _iter_errors. |
| `jsonschema/exceptions.py` | 12 |  | Local minimal/shadow jsonschema compatibility module for exceptions. |
| `jsonschema/validators.py` | 7 |  | Local minimal/shadow jsonschema compatibility module for validators. |

## jsonschema_shadow

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `jsonschema_shadow/__init__.py` | 205 |  | Package initializer for jsonschema_shadow; defines/reexports Draft202012Validator, FormatChecker, RefResolver, _looks_like_ref, _iter_errors. |
| `jsonschema_shadow/exceptions.py` | 12 |  | Local minimal/shadow jsonschema compatibility module for exceptions. |
| `jsonschema_shadow/validators.py` | 7 |  | Local minimal/shadow jsonschema compatibility module for validators. |

## lean

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `lean/DAG/ingest.py` | 75 | yes | Python module/script for ingest; key symbols: ingest. |

## leantrail

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `leantrail/__init__.py` | 3 |  | LeanTrail package. |
| `leantrail/api/__init__.py` | 1 |  | HTTP API surfaces for LeanTrail. |
| `leantrail/api/server.py` | 210 | yes | LeanTrail backend/API component for server; key symbols: LeanTrailRequestHandler, _bool_query, _parse_args, main. |
| `leantrail/backend/__init__.py` | 3 |  | Backend services for LeanTrail. |
| `leantrail/backend/app.py` | 12 | yes | Compatibility entrypoint for LeanTrail API. Prefer `python3 -m leantrail.api.server`. |
| `leantrail/backend/extractor.py` | 17 |  | LeanTrail backend/API component for extractor; key symbols: run_refresh_pipeline. |
| `leantrail/backend/indexer.py` | 314 | yes | LeanTrail backend/API component for indexer; key symbols: _run_git_lines, _safe_git_head, _iter_jsonl, _module_from_lean_path, _detect_changed_modules, _collect_decl_to_module. |
| `leantrail/backend/models.py` | 78 |  | LeanTrail backend/API component for models; key symbols: NodeRecord, EdgeRecord, GraphSnapshot. |
| `leantrail/backend/normalizer.py` | 468 |  | LeanTrail backend/API component for normalizer; key symbols: LeanTrailNormalizer, _utc_now, _read_json, _iter_jsonl, _edge_key, _load_failed_transition_index. |
| `leantrail/backend/query_api.py` | 206 |  | LeanTrail backend/API component for query api; key symbols: LeanTrailQueryAPI, _utc_now, _slug. |
| `leantrail/backend/rpc_adapter.py` | 25 |  | LeanTrail backend/API component for rpc adapter; key symbols: LeanRPCAdapter. |
| `leantrail/backend/store.py` | 257 |  | LeanTrail backend/API component for store; key symbols: GraphStore. |

## presentation

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `presentation/gen_figures.py` | 240 | yes | Python module/script for gen figures; key symbols: _style, _save, gen_kl_divergence, gen_fisher_information, gen_entropy_manifold, _count_lean_files. |

## scratch

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `scratch/test_arango_authority.py` | 16 |  | Python module/script for test Arango authority; key symbols: module-level logic. |

## scripts

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `scripts/__init__.py` | 28 |  | Top-level Python package for active InfoGeometry scripting helpers. This package keeps the still-supported helpers that remain under `scripts/` after archiving the old graph/boo... |
| `scripts/__main__.py` | 4 | yes | Script/support module for  main ; key symbols: module-level logic. |
| `scripts/analysis/filter_project_decls.py` | 100 | yes | Script/support module for filter project decls; key symbols: collect_declared_namespaces, prefix_match, main. |
| `scripts/analysis/lean/__init__.py` | 1 |  | Package initializer for scripts/analysis/lean. |
| `scripts/analysis/lean/catastrophe_surface.py` | 176 | yes | Render finite-temperature free-energy catastrophe surfaces. This script builds the same robust-regression-style finite Gibbs model described in the project notes and visualizes ... |
| `scripts/analysis/utils.py` | 31 | yes | Script/support module for utils; key symbols: load_json, dump_json, prefix_match, sanitize_label_suffix, matches_prefix. |
| `scripts/cli.py` | 48 | yes | Script/support module for CLI; key symbols: main. |
| `scripts/docs/build_doc_map.py` | 215 | yes | Script/support module for build doc map; key symbols: decls_payload_to_list, index_decls, resolve_node, build_resolved, main. |
| `scripts/docs/convert/__init__.py` | 2 |  | Package initializer for scripts/docs/convert. |
| `scripts/docs/convert/common.py` | 171 |  | Script/support module for common; key symbols: BaseSchema, NodePart, FormattingConfig, Node, Position, DeclarationRange. |
| `scripts/docs/convert/main.py` | 169 | yes | Script/support module for main; key symbols: main. |
| `scripts/docs/convert/modify_latex.py` | 65 |  | Script/support module for modify latex; key symbols: write_latex_source. |
| `scripts/docs/convert/modify_lean.py` | 267 |  | Utilities for adding @[blueprint] attributes to Lean source files. |
| `scripts/docs/convert/parse_latex.py` | 308 |  | Script/support module for parse latex; key symbols: SourceInfo, LatexSource, read_latex_file, find_and_remove_command, find_and_remove_command_arguments, find_and_remove_command_argument. |
| `scripts/docs/emit_markdown_index.py` | 96 | yes | Script/support module for emit markdown index; key symbols: main. |
| `scripts/docs/gen_content_auto_tex_from_header.py` | 30 | yes | Script/support module for gen content auto tex from header; key symbols: extract_blueprint_nodes, main. |
| `scripts/docs/proof_gap_report.py` | 211 | yes | Generate a proof-gap report (sorry/axiom) in Markdown and LaTeX. The report is intentionally lightweight and uses only local source text: - finds declarations that are axioms - ... |
| `scripts/intake/parser.py` | 71 | yes | Script/support module for parser; key symbols: LegacyIntakeParser. |
| `scripts/utils.py` | 1 |  | Script/support module for utils; key symbols: module-level logic. |

## skills

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `skills/chatgpt-history-to-hermes/scripts/chatgpt_history_migrate.py` | 211 | yes | Python module/script for chatgpt history migrate; key symbols: safe_text, normalize_role, extract_messages, md_escape, build_memory_candidates, write_jsonl. |

## src

Correction from operator: `src/igf` / `igf` is a failed unfinished refactor. Do not treat this package or CLI as maintained authority from static inventory alone; each specific path must be validated by live tests before use.

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `src/igf/__init__.py` | 1 |  | igf greenfield kernel package. |
| `src/igf/artifacts/__init__.py` | 1 |  | Artifact utilities for igf. |
| `src/igf/artifacts/compatibility_adapters.py` | 153 |  | IGF artifacts module for compatibility adapters; exposes _load_jsonl, _write_jsonl, normalize_run_id, stable_key, _infer_run_id_from_patch_from, normalize_artifacts. |
| `src/igf/artifacts/io.py` | 61 |  | IGF artifacts module for io; exposes sha256_file, sha256_optional_file, read_jsonl, write_json, count_jsonl_rows, file_hashes. |
| `src/igf/artifacts/manifest.py` | 67 |  | IGF artifacts module for manifest; exposes build_manifest, write_manifest. |
| `src/igf/cli.py` | 225 | yes | Canonical igf CLI package entrypoint. |
| `src/igf/config/__init__.py` | 33 |  | Configuration utilities for igf. |
| `src/igf/config/env_aliases.py` | 114 |  | IGF config module for env aliases; exposes repo_root_from, _strip_env_value, load_repo_arango_env, get_env_alias, normalized_arango_env, first_present_name. |
| `src/igf/config/loader.py` | 17 |  | IGF config module for loader; exposes load_arango_config. |
| `src/igf/config/model.py` | 11 |  | IGF config module for model; exposes ArangoConfig. |
| `src/igf/config/preflight.py` | 54 |  | IGF config module for preflight; exposes run_preflight, print_preflight_json. |
| `src/igf/graph/__init__.py` | 45 |  | Arango graph registry and query helpers for igf. |
| `src/igf/graph/arango_client.py` | 44 |  | Canonical IGF command-line entrypoint: dispatches preflight/build/run/validate/normalize/ingest/verify/report/candidate commands. |
| `src/igf/graph/arango_http.py` | 213 |  | IGF graph module for Arango http; exposes ArangoHttpTarget, target_from_config, auth_header, db_url, sys_url, request_json. |
| `src/igf/graph/collections.py` | 15 |  | IGF graph module for collections; exposes support code. |
| `src/igf/graph/indexes.py` | 26 |  | IGF graph module for indexes; exposes support code. |
| `src/igf/graph/query_registry.py` | 246 |  | Canonical AQL query registry for igf greenfield kernel. All operational queries should be referenced by ID and tested via contract fixtures. |
| `src/igf/graph/query_runner.py` | 20 |  | IGF graph module for query runner; exposes run_query, resolve_run_id. |
| `src/igf/pipeline/__init__.py` | 1 |  | Pipeline stages for igf. |
| `src/igf/pipeline/build.py` | 137 |  | IGF pipeline module for build; exposes _repo_root, _parse_summary, resolve_graph_inputs, build_chiral_patches. |
| `src/igf/pipeline/candidates.py` | 88 |  | IGF pipeline module for candidates; exposes find_maxent_style_patch_candidates, find_log_barrier_patch_candidates. |
| `src/igf/pipeline/ingest.py` | 46 |  | IGF pipeline module for ingest; exposes _upsert_document, ingest_artifacts. |
| `src/igf/pipeline/orchestrator.py` | 91 |  | IGF pipeline module for orchestrator; exposes run_offline_pipeline. |
| `src/igf/pipeline/report.py` | 19 |  | IGF pipeline module for report; exposes report_artifacts. |
| `src/igf/pipeline/validate.py` | 108 |  | IGF pipeline module for validate; exposes _load_schema, validate_artifacts. |
| `src/igf/pipeline/verify.py` | 34 |  | IGF pipeline module for verify; exposes verify_run. |
| `src/igf/policy/__init__.py` | 1 |  | Claim-safety policy helpers for igf. |
| `src/igf/policy/claim_scope.py` | 38 |  | IGF policy module for claim scope; exposes apply_default_claim_policy, validate_claim_policy. |

## tests

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `tests/alexandria/test_automathtext_arango_ingest.py` | 101 |  | Pytest/test module exercising automathtext Arango ingest behavior. |
| `tests/alexandria/test_automathtext_v2_ingest.py` | 331 |  | Pytest/test module exercising automathtext v2 ingest behavior. |
| `tests/alexandria/test_conductive_context_to_lean_skeleton.py` | 50 |  | Pytest/test module exercising conductive context to Lean skeleton behavior. |
| `tests/alexandria/test_download_automathtext_v2.py` | 41 |  | Pytest/test module exercising download automathtext v2 behavior. |
| `tests/alexandria/test_fetch_arxiv_corpus.py` | 63 |  | Pytest/test module exercising fetch arxiv corpus behavior. |
| `tests/alexandria/test_graph_context_rank.py` | 99 |  | Pytest/test module exercising graph context rank behavior. |
| `tests/alexandria/test_materialize_coarse_scc_overlay.py` | 53 |  | Pytest/test module exercising materialize coarse scc overlay behavior. |
| `tests/alexandria/test_proof_synthesis_report.py` | 63 |  | Pytest/test module exercising proof synthesis report behavior. |
| `tests/alexandria/test_repair_lineage.py` | 161 |  | Pytest/test module exercising repair lineage behavior. |
| `tests/alexandria/test_retrieve_context.py` | 102 |  | Pytest/test module exercising retrieve context behavior. |
| `tests/alexandria/test_semantic_ingest.py` | 22 |  | Pytest/test module exercising semantic ingest behavior. |
| `tests/alexandria/test_verify_automathtext_arango_descent.py` | 87 |  | Pytest/test module exercising verify automathtext Arango descent behavior. |
| `tests/infra/test_build_chiral_patch_hashes.py` | 204 |  | Pytest/test module exercising build chiral patch hashes behavior. |
| `tests/infra/test_dag_pipeline.py` | 113 |  | Pytest/test module exercising DAG pipeline behavior. |
| `tests/infra/test_env_stability.py` | 15 | yes | Pytest/test module exercising env stability behavior. |
| `tests/infra/test_igf_build_manifest.py` | 98 |  | Pytest/test module exercising IGF build manifest behavior. |
| `tests/infra/test_igf_cli_run_smoke.py` | 37 |  | Pytest/test module exercising IGF CLI run smoke behavior. |
| `tests/infra/test_igf_greenfield_suite.py` | 464 |  | Pytest/test module exercising IGF greenfield suite behavior. |
| `tests/infra/test_igf_ingest_cli_contract.py` | 59 |  | Pytest/test module exercising IGF ingest CLI contract behavior. |
| `tests/infra/test_igf_orchestrator_run.py` | 82 |  | Pytest/test module exercising IGF orchestrator run behavior. |
| `tests/infra/test_igf_run_cli_contract.py` | 59 |  | Pytest/test module exercising IGF run CLI contract behavior. |
| `tests/infra/test_igf_run_json_surface.py` | 120 |  | Pytest/test module exercising IGF run json surface behavior. |
| `tests/infra/test_igf_verify_cli_contract.py` | 129 |  | Pytest/test module exercising IGF verify CLI contract behavior. |
| `tests/test_aesop_tactic_prior.py` | 36 |  | Pytest/test module exercising aesop tactic prior behavior. |
| `tests/test_analyze_stall_distributions.py` | 88 |  | Pytest/test module exercising analyze stall distributions behavior. |
| `tests/test_analyze_tactic_path_ranking.py` | 104 |  | Pytest/test module exercising analyze tactic path ranking behavior. |
| `tests/test_arango_dag_algorithms.py` | 77 | yes | Pytest/test module exercising Arango DAG algorithms behavior. |
| `tests/test_arango_env_wrappers.py` | 84 | yes | Pytest/test module exercising Arango env wrappers behavior. |
| `tests/test_arango_gravity_context.py` | 518 |  | Pytest/test module exercising Arango gravity context behavior. |
| `tests/test_arango_raw_infotree_ingest.py` | 116 |  | Pytest/test module exercising Arango raw infotree ingest behavior. |
| `tests/test_aria_concept_graph.py` | 116 |  | Pytest/test module exercising aria concept graph behavior. |
| `tests/test_aria_scorer_lite.py` | 87 |  | Pytest/test module exercising aria scorer lite behavior. |
| `tests/test_audit_constructivity.py` | 55 | yes | Pytest/test module exercising audit constructivity behavior. |
| `tests/test_blueprint_borrowed_tools.py` | 122 |  | Pytest/test module exercising blueprint borrowed tools behavior. |
| `tests/test_bohm_equilibrium_seed_bridge.py` | 25 |  | Pytest/test module exercising bohm equilibrium seed bridge behavior. |
| `tests/test_bohm_stateqgt_equilibrium_seed_bridge.py` | 14 |  | Pytest/test module exercising bohm stateqgt equilibrium seed bridge behavior. |
| `tests/test_build_tactic_path_ranking_dataset.py` | 186 |  | Pytest/test module exercising build tactic path ranking dataset behavior. |
| `tests/test_build_tactic_training_dataset.py` | 263 |  | Pytest/test module exercising build tactic training dataset behavior. |
| `tests/test_canonical_drazin_singular_star_adapter.py` | 48 |  | Pytest/test module exercising canonical drazin singular star adapter behavior. |
| `tests/test_canonical_moore_penrose_singular_unique_adapter.py` | 44 |  | Pytest/test module exercising canonical moore penrose singular unique adapter behavior. |
| `tests/test_canonical_policy_lint.py` | 26 | yes | Pytest/test module exercising canonical policy lint behavior. |
| `tests/test_cartan_kkt_projector_root_chain.py` | 39 |  | Pytest/test module exercising cartan kkt projector root chain behavior. |
| `tests/test_causal_chiral_prompt_builder.py` | 38 |  | Pytest/test module exercising causal chiral prompt builder behavior. |
| `tests/test_causal_cone_spectrum.py` | 320 |  | Tests for tools/infra/causal_cone_spectrum.py against a synthetic mock DAG. |
| `tests/test_check_resident_model_endpoint.py` | 92 |  | Pytest/test module exercising check resident model endpoint behavior. |
| `tests/test_check_vacuity_policy.py` | 93 | yes | Pytest/test module exercising check vacuity policy behavior. |
| `tests/test_check_vllm_mistral_compat.py` | 54 |  | Pytest/test module exercising check vllm mistral compat behavior. |
| `tests/test_chiral_lightcone_algebra_witness.py` | 29 |  | Pytest/test module exercising chiral lightcone algebra witness behavior. |
| `tests/test_cik_drazin_star_selfadjoint_root_chain.py` | 75 |  | Pytest/test module exercising cik drazin star selfadjoint root chain behavior. |
| `tests/test_cik_selfadjoint_idempotent_constructor.py` | 57 |  | Pytest/test module exercising cik selfadjoint idempotent constructor behavior. |
| `tests/test_clnn_corridor.py` | 112 | yes | Pytest/test module exercising clnn corridor behavior. |
| `tests/test_clnn_specialization_and_metric.py` | 110 | yes | Pytest/test module exercising clnn specialization and metric behavior. |
| `tests/test_closed_range_moore_penrose_existence.py` | 68 |  | Pytest/test module exercising closed range moore penrose existence behavior. |
| `tests/test_compiler_bridge_rpc.py` | 237 | yes | Pytest/test module exercising compiler bridge rpc behavior. |
| `tests/test_conformal_anomaly_projector_commute_iff.py` | 25 | yes | Pytest/test module exercising conformal anomaly projector commute iff behavior. |
| `tests/test_conformal_fisher_square_response_bridge.py` | 16 |  | Pytest/test module exercising conformal fisher square response bridge behavior. |
| `tests/test_conformal_operator_admissibility_witness.py` | 16 |  | Pytest/test module exercising conformal operator admissibility witness behavior. |
| `tests/test_conformal_projector_agreement.py` | 70 | yes | Pytest/test module exercising conformal projector agreement behavior. |
| `tests/test_coordinateless_souriau_kms_cyclic_branch.py` | 29 |  | Pytest/test module exercising coordinateless souriau kms cyclic branch behavior. |
| `tests/test_cp1_drazin_model_residue_root_chain.py` | 17 |  | Pytest/test module exercising cp1 drazin model residue root chain behavior. |
| `tests/test_decl_graph_support.py` | 121 | yes | Pytest/test module exercising decl graph support behavior. |
| `tests/test_density_weight_equilibrium_bridge_theorems.py` | 15 |  | Pytest/test module exercising density weight equilibrium bridge theorems behavior. |
| `tests/test_drazin_chiral_supertrace_owner.py` | 33 |  | Pytest/test module exercising drazin chiral supertrace owner behavior. |
| `tests/test_drazin_operator_corridor.py` | 103 | yes | Pytest/test module exercising drazin operator corridor behavior. |
| `tests/test_drazin_root_owner_chain.py` | 33 |  | Pytest/test module exercising drazin root owner chain behavior. |
| `tests/test_drazin_supergraded_translation_packet.py` | 55 | yes | Pytest/test module exercising drazin supergraded translation packet behavior. |
| `tests/test_enrich_tactic_path_operator_spectrum.py` | 182 |  | Pytest/test module exercising enrich tactic path operator spectrum behavior. |
| `tests/test_enrich_tactic_path_with_lightcone_spectrum.py` | 63 |  | Pytest/test module exercising enrich tactic path with lightcone spectrum behavior. |
| `tests/test_fierz_area_root_chain.py` | 33 |  | Pytest/test module exercising fierz area root chain behavior. |
| `tests/test_fierz_owner_root_chain.py` | 32 |  | Pytest/test module exercising fierz owner root chain behavior. |
| `tests/test_fierz_projection_boundary.py` | 56 |  | Pytest/test module exercising fierz projection boundary behavior. |
| `tests/test_fitting_drazin_boundary.py` | 60 |  | Pytest/test module exercising fitting drazin boundary behavior. |
| `tests/test_gemini_cli_guard.py` | 93 |  | Pytest/test module exercising gemini CLI guard behavior. |
| `tests/test_generalized_metric_core.py` | 127 | yes | Pytest/test module exercising generalized metric core behavior. |
| `tests/test_generalized_metric_polarized_bridge.py` | 103 | yes | Pytest/test module exercising generalized metric polarized bridge behavior. |
| `tests/test_generalized_metric_recomposition_bridge.py` | 118 | yes | Pytest/test module exercising generalized metric recomposition bridge behavior. |
| `tests/test_generate_theory_spire_viz.py` | 34 | yes | Pytest/test module exercising generate theory spire viz behavior. |
| `tests/test_generate_truth_transport.py` | 76 |  | Pytest/test module exercising generate truth transport behavior. |
| `tests/test_gromov_witten_projective_lane_targets.py` | 23 |  | Pytest/test module exercising gromov witten projective lane targets behavior. |
| `tests/test_hermes_bounded_runner.py` | 81 |  | Pytest/test module exercising hermes bounded runner behavior. |
| `tests/test_hermes_leanstral_autoproof_loop.py` | 164 |  | Pytest/test module exercising hermes leanstral autoproof loop behavior. |
| `tests/test_hermes_vibe_coding_agent.py` | 134 |  | Pytest/test module exercising hermes vibe coding agent behavior. |
| `tests/test_hestenes_dilation_charge_mode.py` | 21 |  | Pytest/test module exercising hestenes dilation charge mode behavior. |
| `tests/test_hestenes_dirac_formalization.py` | 155 |  | Pytest/test module exercising hestenes dirac formalization behavior. |
| `tests/test_hive_arango_queue.py` | 151 |  | Pytest/test module exercising Hive Arango queue behavior. |
| `tests/test_hive_autoproof_trace_schemas.py` | 281 |  | Pytest/test module exercising Hive autoproof trace schemas behavior. |
| `tests/test_hive_bee.py` | 492 |  | Pytest/test module exercising Hive bee behavior. |
| `tests/test_hive_bee_runner.py` | 360 |  | Pytest/test module exercising Hive bee runner behavior. |
| `tests/test_hive_bee_task_result_schemas.py` | 369 |  | Pytest/test module exercising Hive bee task result schemas behavior. |
| `tests/test_hive_cognitive_packet_schemas.py` | 145 |  | Pytest/test module exercising Hive cognitive packet schemas behavior. |
| `tests/test_hive_json_ingestor.py` | 110 |  | Pytest/test module exercising Hive json ingestor behavior. |
| `tests/test_hive_leanstral_bee_worker.py` | 304 |  | Pytest/test module exercising Hive leanstral bee worker behavior. |
| `tests/test_hive_local_packet_store.py` | 162 |  | Pytest/test module exercising Hive local packet store behavior. |
| `tests/test_hive_logos_semantics.py` | 26 |  | Pytest/test module exercising Hive logos semantics behavior. |
| `tests/test_hive_logos_tracer.py` | 18 |  | Pytest/test module exercising Hive logos tracer behavior. |
| `tests/test_hive_motherbee.py` | 572 |  | Pytest/test module exercising Hive motherbee behavior. |
| `tests/test_hive_multichecker_merge.py` | 97 |  | Pytest/test module exercising Hive multichecker merge behavior. |
| `tests/test_hive_spec_submission_policy.py` | 201 |  | Pytest/test module exercising Hive spec submission policy behavior. |
| `tests/test_hive_swarm.py` | 131 |  | Pytest/test module exercising Hive swarm behavior. |
| `tests/test_hive_translation_control_packet.py` | 89 |  | Pytest/test module exercising Hive translation control packet behavior. |
| `tests/test_hive_workflow_policy.py` | 116 |  | Pytest/test module exercising Hive workflow policy behavior. |
| `tests/test_hydrate_arango_topology.py` | 77 |  | Pytest/test module exercising hydrate Arango topology behavior. |
| `tests/test_hydrated_dag_to_lean_graph.py` | 196 |  | Pytest/test module exercising hydrated DAG to Lean graph behavior. |
| `tests/test_improver_external_stack.py` | 67 |  | Pytest/test module exercising improver external stack behavior. |
| `tests/test_improver_trace_bridge.py` | 84 |  | Pytest/test module exercising improver trace bridge behavior. |
| `tests/test_incompressible_bit_bridge.py` | 40 |  | Pytest/test module exercising incompressible bit bridge behavior. |
| `tests/test_incompressible_cramer_rao_action_bridge.py` | 63 |  | Pytest/test module exercising incompressible cramer rao action bridge behavior. |
| `tests/test_infinite_owner_hessian_context.py` | 82 |  | Pytest/test module exercising infinite owner hessian context behavior. |
| `tests/test_infinite_owner_kms_context.py` | 90 |  | Pytest/test module exercising infinite owner kms context behavior. |
| `tests/test_ingest_semantic_content_audit.py` | 137 |  | Pytest/test module exercising ingest semantic content audit behavior. |
| `tests/test_injection_common_gpu_snapshot.py` | 24 |  | Pytest/test module exercising injection common gpu snapshot behavior. |
| `tests/test_jixia_batch_training.py` | 214 |  | Pytest/test module exercising jixia batch training behavior. |
| `tests/test_jixia_trace_bridge.py` | 176 |  | Pytest/test module exercising jixia trace bridge behavior. |
| `tests/test_kanban_evidence_lint.py` | 84 |  | Pytest/test module exercising kanban evidence lint behavior. |
| `tests/test_kkt_corridor.py` | 164 | yes | Pytest/test module exercising kkt corridor behavior. |
| `tests/test_kkt_exact_residual_packet.py` | 12 |  | Pytest/test module exercising kkt exact residual packet behavior. |
| `tests/test_kkt_stationarity_exact_branch.py` | 12 |  | Pytest/test module exercising kkt stationarity exact branch behavior. |
| `tests/test_lean_auto_trace_bridge.py` | 83 |  | Pytest/test module exercising Lean auto trace bridge behavior. |
| `tests/test_lean_autograder_report_bridge.py` | 65 |  | Pytest/test module exercising Lean autograder report bridge behavior. |
| `tests/test_lean_improver_probe.py` | 54 |  | Pytest/test module exercising Lean improver probe behavior. |
| `tests/test_lean_interact_wrapper.py` | 25 |  | Pytest/test module exercising Lean interact wrapper behavior. |
| `tests/test_leandojo_v2_bridge.py` | 178 |  | Pytest/test module exercising leandojo v2 bridge behavior. |
| `tests/test_leanparanoia_audit_bridge.py` | 65 |  | Pytest/test module exercising leanparanoia audit bridge behavior. |
| `tests/test_leansearch_local.py` | 72 |  | Pytest/test module exercising leansearch local behavior. |
| `tests/test_lightcone_spectral_filter.py` | 80 |  | Pytest/test module exercising lightcone spectral filter behavior. |
| `tests/test_logipedia_markdown_distill.py` | 180 |  | Pytest/test module exercising logipedia markdown distill behavior. |
| `tests/test_logsumexp_hol_derivative_root_chain.py` | 41 |  | Pytest/test module exercising logsumexp hol derivative root chain behavior. |
| `tests/test_majorana_equilibrium_seed_bridge.py` | 21 |  | Pytest/test module exercising majorana equilibrium seed bridge behavior. |
| `tests/test_mathfulness_audit.py` | 138 |  | Pytest/test module exercising mathfulness audit behavior. |
| `tests/test_metric_transport_witness.py` | 80 | yes | Pytest/test module exercising metric transport witness behavior. |
| `tests/test_millennium_problem_bridge.py` | 86 |  | Pytest/test module exercising millennium problem bridge behavior. |
| `tests/test_moore_penrose_projector_own_range_adapter.py` | 71 |  | Pytest/test module exercising moore penrose projector own range adapter behavior. |
| `tests/test_moore_penrose_root_projector_chain.py` | 39 |  | Pytest/test module exercising moore penrose root projector chain behavior. |
| `tests/test_neutral_phase_space_corridor.py` | 100 | yes | Pytest/test module exercising neutral phase space corridor behavior. |
| `tests/test_observer_defect_strain_zero_bridge.py` | 15 |  | Pytest/test module exercising observer defect strain zero bridge behavior. |
| `tests/test_onsager_equilibrium_seed_bridge.py` | 19 |  | Pytest/test module exercising onsager equilibrium seed bridge behavior. |
| `tests/test_open_problem_formalization.py` | 224 | yes | Pytest/test module exercising open problem formalization behavior. |
| `tests/test_operator_owner_map_v2.py` | 117 | yes | Pytest/test module exercising operator owner map v2 behavior. |
| `tests/test_operatorial_dilation_goldstone_charge_packet.py` | 16 |  | Pytest/test module exercising operatorial dilation goldstone charge packet behavior. |
| `tests/test_operatorial_partition_supervolume_bridge_owner_theorem.py` | 21 |  | Pytest/test module exercising operatorial partition supervolume bridge owner theorem behavior. |
| `tests/test_operatorial_souriau_fisher_metric_packet.py` | 16 |  | Pytest/test module exercising operatorial souriau fisher metric packet behavior. |
| `tests/test_operatorial_weyl_supercharacter_bridge.py` | 22 |  | Pytest/test module exercising operatorial weyl supercharacter bridge behavior. |
| `tests/test_paperproof_bidirectional_cone.py` | 107 |  | Pytest/test module exercising paperproof bidirectional cone behavior. |
| `tests/test_paperproof_jixia_compare.py` | 81 |  | Pytest/test module exercising paperproof jixia compare behavior. |
| `tests/test_paperproof_proof_forest.py` | 82 |  | Pytest/test module exercising paperproof proof forest behavior. |
| `tests/test_paperproof_rpc_export_schema.py` | 55 |  | Pytest/test module exercising paperproof rpc export schema behavior. |
| `tests/test_paperproof_tableau_detector.py` | 66 |  | Pytest/test module exercising paperproof tableau detector behavior. |
| `tests/test_paperproof_trace_bridge.py` | 89 |  | Pytest/test module exercising paperproof trace bridge behavior. |
| `tests/test_pda_forml4_bridge.py` | 79 |  | Pytest/test module exercising pda forml4 bridge behavior. |
| `tests/test_phase_a_full_suite.py` | 246 |  | Pytest/test module exercising phase a full suite behavior. |
| `tests/test_phase_a_leandojo_l0.py` | 58 |  | Pytest/test module exercising phase a leandojo l0 behavior. |
| `tests/test_phase_space_causal_flow_bridge.py` | 158 | yes | Pytest/test module exercising phase space causal flow bridge behavior. |
| `tests/test_phase_space_conformal_kkt_bridge.py` | 146 | yes | Pytest/test module exercising phase space conformal kkt bridge behavior. |
| `tests/test_phase_space_generalized_metric.py` | 141 | yes | Pytest/test module exercising phase space generalized metric behavior. |
| `tests/test_phase_space_recomposition_bridge.py` | 333 | yes | Pytest/test module exercising phase space recomposition bridge behavior. |
| `tests/test_phase_space_recomposition_example.py` | 133 | yes | Pytest/test module exercising phase space recomposition example behavior. |
| `tests/test_phase_space_weyl_causal_bridge.py` | 302 | yes | Pytest/test module exercising phase space weyl causal bridge behavior. |
| `tests/test_ported_operator_bridges.py` | 48 |  | Pytest/test module exercising ported operator bridges behavior. |
| `tests/test_positive_adjoint_square_boundary.py` | 62 |  | Pytest/test module exercising positive adjoint square boundary behavior. |
| `tests/test_predigestion_packets.py` | 111 |  | Pytest/test module exercising predigestion packets behavior. |
| `tests/test_projector_anomaly_transport_sync_v2.py` | 83 | yes | Pytest/test module exercising projector anomaly transport sync v2 behavior. |
| `tests/test_projector_noncommutativity_dilation_closure.py` | 84 | yes | Pytest/test module exercising projector noncommutativity dilation closure behavior. |
| `tests/test_real_prover_trace_bridge.py` | 89 |  | Pytest/test module exercising real prover trace bridge behavior. |
| `tests/test_refresh_blueprint_tags.py` | 44 | yes | Pytest/test module exercising refresh blueprint tags behavior. |
| `tests/test_relative_modular_recomposition.py` | 131 | yes | Pytest/test module exercising relative modular recomposition behavior. |
| `tests/test_representation_depth_export.py` | 255 | yes | Pytest/test module exercising representation depth export behavior. |
| `tests/test_rethlas_verification_bridge.py` | 94 |  | Pytest/test module exercising rethlas verification bridge behavior. |
| `tests/test_run_copilot_codex_lean_pipeline.py` | 43 |  | Pytest/test module exercising run copilot codex Lean pipeline behavior. |
| `tests/test_run_gemini_guarded.py` | 67 |  | Pytest/test module exercising run gemini guarded behavior. |
| `tests/test_run_predigestion_to_hive_demo.py` | 73 |  | Pytest/test module exercising run predigestion to Hive demo behavior. |
| `tests/test_run_proof_prompt_batch.py` | 109 |  | Pytest/test module exercising run proof prompt batch behavior. |
| `tests/test_safeverify_audit_bridge.py` | 83 |  | Pytest/test module exercising safeverify audit bridge behavior. |
| `tests/test_selfdual_chiral_partition_witness.py` | 21 |  | Pytest/test module exercising selfdual chiral partition witness behavior. |
| `tests/test_semantic_content_audit.py` | 161 |  | Pytest/test module exercising semantic content audit behavior. |
| `tests/test_sinkhorn_clock_defect_constructive_bound.py` | 53 |  | Pytest/test module exercising sinkhorn clock defect constructive bound behavior. |
| `tests/test_sinkhorn_rn_barrier_comparison_constructor.py` | 14 |  | Pytest/test module exercising sinkhorn rn barrier comparison constructor behavior. |
| `tests/test_sinkhorn_zd_controlled_observer_equilibrium.py` | 15 |  | Pytest/test module exercising sinkhorn zd controlled observer equilibrium behavior. |
| `tests/test_souriau_claimA_root_chain.py` | 29 |  | Pytest/test module exercising souriau claimA root chain behavior. |
| `tests/test_souriau_conformal_chiral_scale_bridge.py` | 20 |  | Pytest/test module exercising souriau conformal chiral scale bridge behavior. |
| `tests/test_souriau_conformal_equilibrium_seed.py` | 14 |  | Pytest/test module exercising souriau conformal equilibrium seed behavior. |
| `tests/test_souriau_first_variation_weyl_bridge.py` | 18 |  | Pytest/test module exercising souriau first variation weyl bridge behavior. |
| `tests/test_souriau_kkt_exact_residual_translator.py` | 36 |  | Pytest/test module exercising souriau kkt exact residual translator behavior. |
| `tests/test_souriau_metriplectic_square_translator.py` | 34 |  | Pytest/test module exercising souriau metriplectic square translator behavior. |
| `tests/test_souriau_operatorial_log_potential.py` | 103 | yes | Pytest/test module exercising souriau operatorial log potential behavior. |
| `tests/test_souriau_thermodynamic_readout_seed_bridge.py` | 14 |  | Pytest/test module exercising souriau thermodynamic readout seed bridge behavior. |
| `tests/test_souriau_tomita_modular_flow_bridge.py` | 67 |  | Pytest/test module exercising souriau tomita modular flow bridge behavior. |
| `tests/test_souriau_translator_identity_balanced_stress.py` | 15 |  | Pytest/test module exercising souriau translator identity balanced stress behavior. |
| `tests/test_souriau_weyl_partition.py` | 105 | yes | Pytest/test module exercising souriau weyl partition behavior. |
| `tests/test_souriau_weyl_supertrace_corrected.py` | 138 | yes | Pytest/test module exercising souriau weyl supertrace corrected behavior. |
| `tests/test_souriau_weyl_supertrace_layer.py` | 88 | yes | Pytest/test module exercising souriau weyl supertrace layer behavior. |
| `tests/test_spin44_character_shadow.py` | 28 |  | Pytest/test module exercising spin44 character shadow behavior. |
| `tests/test_strict_def.py` | 148 | yes | Pytest/test module exercising strict def behavior. |
| `tests/test_strict_surface.py` | 177 | yes | Pytest/test module exercising strict surface behavior. |
| `tests/test_super_souriau_identity_balanced_stress.py` | 14 |  | Pytest/test module exercising super souriau identity balanced stress behavior. |
| `tests/test_supercharge_transport_translation_packet.py` | 86 | yes | Pytest/test module exercising supercharge transport translation packet behavior. |
| `tests/test_supermetriplectic_bps_build.py` | 24 | yes | Pytest/test module exercising supermetriplectic bps build behavior. |
| `tests/test_supermetriplectic_cartan_bridge.py` | 44 | yes | Pytest/test module exercising supermetriplectic cartan bridge behavior. |
| `tests/test_supermetriplectic_chiral_bridge.py` | 49 | yes | Pytest/test module exercising supermetriplectic chiral bridge behavior. |
| `tests/test_supermetriplectic_chiral_scalar_closure.py` | 47 | yes | Pytest/test module exercising supermetriplectic chiral scalar closure behavior. |
| `tests/test_supermetriplectic_drazin_bridge.py` | 51 | yes | Pytest/test module exercising supermetriplectic drazin bridge behavior. |
| `tests/test_supermetriplectic_drazin_projector_constraint_bridge.py` | 47 | yes | Pytest/test module exercising supermetriplectic drazin projector constraint bridge behavior. |
| `tests/test_supermetriplectic_entropy_shadow_bridge.py` | 43 | yes | Pytest/test module exercising supermetriplectic entropy shadow bridge behavior. |
| `tests/test_supermetriplectic_inverse_bridge.py` | 43 | yes | Pytest/test module exercising supermetriplectic inverse bridge behavior. |
| `tests/test_supermetriplectic_triad_bridge.py` | 61 | yes | Pytest/test module exercising supermetriplectic triad bridge behavior. |
| `tests/test_theorem_significance.py` | 522 | yes | Pytest/test module exercising theorem significance behavior. |
| `tests/test_theory_shadow_representation.py` | 40 |  | Pytest/test module exercising theory shadow representation behavior. |
| `tests/test_thermodynamic_generator_equilibrium_seed_bridge.py` | 12 |  | Pytest/test module exercising thermodynamic generator equilibrium seed bridge behavior. |
| `tests/test_thermodynamic_generator_first_variation_pair.py` | 14 |  | Pytest/test module exercising thermodynamic generator first variation pair behavior. |
| `tests/test_triality_moe_aligned_owner_bound.py` | 20 |  | Pytest/test module exercising triality moe aligned owner bound behavior. |
| `tests/test_triality_moe_compressed_deviation_zero_constructor.py` | 17 |  | Pytest/test module exercising triality moe compressed deviation zero constructor behavior. |
| `tests/test_triality_moe_constructive_bound.py` | 14 |  | Pytest/test module exercising triality moe constructive bound behavior. |
| `tests/test_triality_moe_deviation_zero_constructive_bound.py` | 18 |  | Pytest/test module exercising triality moe deviation zero constructive bound behavior. |
| `tests/test_triality_moe_deviation_zero_constructor_flow.py` | 17 |  | Pytest/test module exercising triality moe deviation zero constructor flow behavior. |
| `tests/test_triality_moe_deviation_zero_owner_bound.py` | 20 |  | Pytest/test module exercising triality moe deviation zero owner bound behavior. |
| `tests/test_triality_moe_general_constructive_bound.py` | 25 |  | Pytest/test module exercising triality moe general constructive bound behavior. |
| `tests/test_triality_moe_residual_zero_constructor_flow.py` | 20 |  | Pytest/test module exercising triality moe residual zero constructor flow behavior. |
| `tests/test_triality_moe_strain_zero_constructor_flow.py` | 19 |  | Pytest/test module exercising triality moe strain zero constructor flow behavior. |
| `tests/test_triality_moe_zd_controlled_constructor_flow.py` | 18 |  | Pytest/test module exercising triality moe zd controlled constructor flow behavior. |
| `tests/test_ulam_trace_bridge.py` | 109 |  | Pytest/test module exercising ulam trace bridge behavior. |
| `tests/test_vacuity_lint.py` | 76 | yes | Pytest/test module exercising vacuity lint behavior. |
| `tests/test_vacuity_planner.py` | 978 | yes | Pytest/test module exercising vacuity planner behavior. |
| `tests/test_vandermonde_root_chain.py` | 37 |  | Pytest/test module exercising vandermonde root chain behavior. |
| `tests/test_weighted_weyl_equilibrium_bridge_theorems.py` | 15 |  | Pytest/test module exercising weighted weyl equilibrium bridge theorems behavior. |
| `tests/test_weyl_zero_scale_collapse.py` | 11 |  | Pytest/test module exercising weyl zero scale collapse behavior. |
| `tests/test_weyl_zero_scale_semantic_packet.py` | 11 |  | Pytest/test module exercising weyl zero scale semantic packet behavior. |
| `tests/test_winding_constructive_forcing.py` | 17 |  | Pytest/test module exercising winding constructive forcing behavior. |

## tools

| Path | LOC | Entry? | Description |
|---|---:|:---:|---|
| `tools/__init__.py` | 2 |  | TIR (Tool-Integrated Reasoning) layer for the Info-Geometry Spire. |
| `tools/alexandria/__init__.py` | 1 |  | Alexandria digestion and retrieval pipeline. |
| `tools/alexandria/alexandria_algorithms.py` | 422 | yes | Runs alexandria algorithms tooling in tools/alexandria; key symbols: AlexandriaGraph, stable_hash, read_jsonl, chunk_key_from_doc_id, canonical_entity_key, build_graph. |
| `tools/alexandria/arango_ingest.py` | 163 | yes | Runs Arango ingest tooling in tools/alexandria; key symbols: auth_header, request_json, sys_url, db_url, ensure_database, ensure_collection. |
| `tools/alexandria/automathtext_arango_ingest.py` | 358 | yes | Ingest AutoMathText-V2 Alexandria theorem-context JSONL into ArangoDB. This loader is for the generic `automath_*` epistemic ancestry graph emitted by `automathtext_v2_ingest.py... |
| `tools/alexandria/automathtext_v2_ingest.py` | 1273 | yes | Convert AutoMathText-V2 shards/rows into Alexandria theorem-context graph JSONL. This is a deterministic v0 intake layer. It preserves raw fragments, then emits smaller theorem-... |
| `tools/alexandria/conductive_context_to_lean_skeleton.py` | 279 | yes | Runs conductive context to Lean skeleton tooling in tools/alexandria; key symbols: LeanCandidate, stable_hash, load_packet, sanitize_name, edge_terms, candidate_statement. |
| `tools/alexandria/download_automathtext_v2.py` | 210 | yes | Runs download automathtext v2 tooling in tools/alexandria; key symbols: DownloadPlan, normalize_config, pattern_for_config, build_allow_patterns, make_plan, import_huggingface_hub. |
| `tools/alexandria/fetch_arxiv_corpus.py` | 335 | yes | Runs fetch arxiv corpus tooling in tools/alexandria; key symbols: strip_tex_comments, strip_tex_preamble, drop_tex_environments, strip_macro_definitions, clean_tex_braces, protect_math_segments. |
| `tools/alexandria/graph_context_rank.py` | 534 | yes | Runs graph context rank tooling in tools/alexandria; key symbols: maybe_enable_gpu_backend, tokenize, read_jsonl, lexical_score, chunk_key_from_doc_id, entity_bonus. |
| `tools/alexandria/materialize_coarse_scc_overlay.py` | 173 | yes | Runs materialize coarse scc overlay tooling in tools/alexandria; key symbols: edge_preview, collect_entities_for_chunk, representative_terms, write_jsonl, materialize, main. |
| `tools/alexandria/proof_synthesis_report.py` | 228 | yes | Runs proof synthesis report tooling in tools/alexandria; key symbols: _text, execute_aql, flatten_witnesses, select_top_path, render_prompt, build_packet. |
| `tools/alexandria/render_socratic_dossier.py` | 97 | yes | Runs render socratic dossier tooling in tools/alexandria; key symbols: load_packet, render_hit, render_dossier, main. |
| `tools/alexandria/repair_lineage.py` | 301 | yes | Runs repair lineage tooling in tools/alexandria; key symbols: GateResult, RepairAttempt, node_collection, node_key, arango_id, run_gate. |
| `tools/alexandria/retrieve_context.py` | 96 | yes | Runs retrieve context tooling in tools/alexandria; key symbols: tokenize, read_jsonl, score, main. |
| `tools/alexandria/schema.py` | 61 |  | Provides schema tooling in tools/alexandria; key symbols: stable_key, content_hash, infer_source_kind, source_uri. |
| `tools/alexandria/semantic_ingest.py` | 492 | yes | Runs semantic ingest tooling in tools/alexandria; key symbols: Section, Chunk, Entity, Relation, stable_key, normalize_surface. |
| `tools/alexandria/structural_chunking.py` | 617 |  | Provides structural chunking tooling in tools/alexandria; key symbols: StructuralSection, StructuralChunk, ChunkingResult, tokenize, base_provenance, adjacent_edge. |
| `tools/alexandria/txt2kg_hive_ingest.py` | 1043 | yes | Digest text libraries into retrieval-only KG triples and Hive tasks. This is the repo-native adaptation of the NVIDIA txt2kg pattern: documents -> chunks -> triples -> predigest... |
| `tools/alexandria/verify_automathtext_arango_descent.py` | 338 | yes | Verify AutoMathText-V2 epistemic ancestry descent in ArangoDB. Non-mutating verifier for the generic `automath_*` sidecar graph imported by `automathtext_arango_ingest.py`. It c... |
| `tools/build_lock.py` | 102 | yes | Provides build lock tooling in tools/root; key symbols: BuildLockBusyError, BuildLock, read_lock_metadata, acquire_build_lock. |
| `tools/check_bipartite_bleed.py` | 11 | yes | Runs check bipartite bleed tooling in tools/root; key symbols: module-level logic. |
| `tools/check_vacuity_policy.py` | 168 | yes | Vacuity Policy Gate — Layer C of the vacuity enforcement system. Reads the JSON report produced by ``theorem_significance.py`` and enforces the repository policy: any "error"-le... |
| `tools/classify_missing_all.py` | 10 | yes | Runs classify missing all tooling in tools/root; key symbols: module-level logic. |
| `tools/docs/__init__.py` | 1 |  | Maintained documentation orchestration and generated status surfaces. |
| `tools/docs/generate_auto_docs.py` | 309 | yes | Runs generate auto docs tooling in tools/docs; key symbols: ModuleSummary, load_json, count_lean_files_and_loc, summarize_module, module_table_rows, seed_bridge_summary. |
| `tools/docs/refresh_markdown_status.py` | 267 | yes | Runs refresh markdown status tooling in tools/docs; key symbols: StatusSpec, repo_markdown_files, all_candidate_markdown_files, should_manage, classify, relative_link. |
| `tools/docs/update_repo_docs.py` | 333 | yes | Runs update repo docs tooling in tools/docs; key symbols: ExportSpec, run, ensure_exists, normalize_repo_relative, export_spec_for_paths, existing_export_specs. |
| `tools/extract_module_patch.py` | 10 | yes | Runs extract module patch tooling in tools/root; key symbols: module-level logic. |
| `tools/failure_correction_driver.py` | 795 | yes | Runs failure correction driver tooling in tools/root; key symbols: CommandResult, RepairAttempt, parse_args, load_text, load_json, tail_text. |
| `tools/frontier/__init__.py` | 1 |  | Maintained semantic-export and frontier-analysis tooling. |
| `tools/frontier/compiler_bridge_client.py` | 564 | yes | Runs compiler bridge client tooling in tools/frontier; key symbols: CompilerBridgeSession, log_stage, server_command, normalize_result, infer_decl_position_in_text, resolve_bridge_position. |
| `tools/frontier/extract_module_patch.py` | 599 | yes | Runs extract module patch tooling in tools/frontier; key symbols: is_noise_decl, parse_args, default_out_paths, as_int, load_decl_meta, load_surface_rows. |
| `tools/frontier/proof_print.py` | 108 | yes | Runs proof print tooling in tools/frontier; key symbols: parse_args, main. |
| `tools/frontier/proof_runtime.py` | 122 | yes | Provides proof runtime tooling in tools/frontier; key symbols: BridgeCallSpec, call_spec_for_print_mode, extract_print_text, build_prewarm_request, summarize_bridge_response. |
| `tools/frontier/proof_session.py` | 250 | yes | Runs proof session tooling in tools/frontier; key symbols: emit, parse_args, request_error, handle_request, main. |
| `tools/frontier/semantic_block_export.py` | 496 | yes | Runs semantic block export tooling in tools/frontier; key symbols: JsonRpcError, LspClient, server_command, log_stage, inject_rpc_import, adjust_stable_id. |
| `tools/frontier/semantic_snapshot.py` | 750 | yes | Runs semantic snapshot tooling in tools/frontier; key symbols: log_stage, snapshot_server_command, inject_snapshot_imports, normalize_semantic_payload, normalize_bridge_payload, module_name_guess. |
| `tools/frontier/skynet_v2.py` | 651 | yes | Runs skynet v2 tooling in tools/frontier; key symbols: Edge, AuditFinding, SemanticWeb, semantic_json_paths, load_payload, normalize_source_file. |
| `tools/generate_auto_docs.py` | 10 | yes | Runs generate auto docs tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_bridge_candidates.py` | 10 | yes | Runs generate bridge candidates tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_bridge_thinness_index.py` | 10 | yes | Runs generate bridge thinness index tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_causal_report.py` | 10 | yes | Runs generate causal report tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_debt_candidates.py` | 10 | yes | Runs generate debt candidates tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_llm_debt_prompts.py` | 10 | yes | Runs generate LLM debt prompts tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_llm_frontier_prompts.py` | 10 | yes | Runs generate LLM frontier prompts tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_self_optimization_report.py` | 10 | yes | Runs generate self optimization report tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_source_sink_compression.py` | 11 | yes | Runs generate source sink compression tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_structural_dedup.py` | 11 | yes | Runs generate structural dedup tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_structural_fibers.py` | 11 | yes | Runs generate structural fibers tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_surrogate_index.py` | 10 | yes | Runs generate surrogate index tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_unification_index.py` | 10 | yes | Runs generate unification index tooling in tools/root; key symbols: module-level logic. |
| `tools/generate_vacuity_index.py` | 10 | yes | Runs generate vacuity index tooling in tools/root; key symbols: module-level logic. |
| `tools/graph.py` | 45 | yes | Compatibility shim for the archived declaration-graph wrapper. This module is no longer the canonical causal-order surface of the repository. The current authoritative declarati... |
| `tools/ig.py` | 114 | yes | Info-Geometry Spire Orchestrator (IG-CLI) Central entrypoint for the Level 3 Greenfield Architecture. |
| `tools/igf.py` | 18 | yes | Compatibility wrapper for the package-local igf CLI. |
| `tools/infra/__init__.py` | 1 |  | Core maintenance and diagnostic infrastructure for the Spire. |
| `tools/infra/aesop_tactic_prior.py` | 154 | yes | Aesop-inspired static tactic prior classification. Aesop separates proof search into normalisation, safe rules, and unsafe backtracking rules. This module borrows that control v... |
| `tools/infra/agentic_policy_lint.py` | 219 | yes | Runs agentic policy lint tooling in tools/infra; key symbols: _as_dict, _as_list, _must_contain, _load_yaml, _check_linkage, _check_runtime_policy. |
| `tools/infra/alchemical_loop.py` | 68 | yes | Runs alchemical loop tooling in tools/infra; key symbols: run_command, auto_promote, main. |
| `tools/infra/analyze_stall_distributions.py` | 164 | yes | Analyze bottlenecks in tactic path ranking telemetry. Reads info_geometry.tactic_path_ranking.v1 JSONL plus optional summary JSON and emits a compact report for stall/failure co... |
| `tools/infra/analyze_tactic_path_ranking.py` | 246 | yes | Analyze tactic path ranking datasets before reranker training. This script inspects the Spectral-Journey-style ranking rows emitted by build_tactic_path_ranking_dataset.py. It m... |
| `tools/infra/apex_defect_profile.py` | 874 | yes | Apex-local defect profiler on the SCC-condensed declaration DAG. For a given apex, computes a structured **obstruction dossier** rather than a single importance score. Each doss... |
| `tools/infra/arango_causal_chiral_cone_prompt.py` | 483 | yes | Emit a causal/chiral cone prompt packet for one Lean declaration. This tool is a prompt-shaping layer over the existing Arango-DAG overlays. It does not prove anything. It perfo... |
| `tools/infra/arango_dag_algorithms.py` | 2288 | yes | Run DAG graph algorithms over the live Arango topology overlay. This is a derived overlay engine. It does not rewrite raw graph collections and does not replace the Lean-owned D... |
| `tools/infra/arango_env.py` | 43 |  | Compatibility wrapper for shared Arango environment loading. The canonical implementation lives in ``igf.config``. This module remains so legacy tools can keep importing ``tools... |
| `tools/infra/arango_fidelity_audit.py` | 171 | yes | Audit how faithful the current Arango graph is to local graph artifacts. The existing `ig_nodes`/`ig_edges` collections are a retrieval projection. This tool makes that explicit... |
| `tools/infra/arango_gravity_context.py` | 1410 | yes | Build Lean-grounded "gravitational" context from the proven declaration graph. The tool prefers live ArangoDB collections, but falls back to the repo's LeanTrail JSONL export. I... |
| `tools/infra/arango_layered_ingest.py` | 290 | yes | Ingest hydrated raw graph and topology overlay JSONL into ArangoDB. This keeps the layered tensor-network model intact: - raw nodes/edges are imported one-for-one into raw colle... |
| `tools/infra/arango_raw_infotree_graph.py` | 303 | yes | Create/probe a named ArangoDB graph for raw_infotree_* collections. This is the handoff point from loss-audited compiler-memory rows to graph analytics tooling. The named graph ... |
| `tools/infra/arango_raw_infotree_ingest.py` | 1011 | yes | Ingest stage raw_infotree_* JSONL exports into ArangoDB. This is intentionally separate from ``arango_layered_ingest.py``. The layered ingester imports the lossless raw DAG depe... |
| `tools/infra/arango_structural_vacuity_audit.py` | 460 | yes | Runs Arango structural vacuity audit tooling in tools/infra; key symbols: collection_name, positive_int, request_json, run_aql, build_query, make_report. |
| `tools/infra/aria_concept_graph.py` | 312 | yes | Aria-style concept graph builder over local LeanSearch records. This is a planning/grounding artifact, not proof authority. It borrows Aria's useful shape: informal claim -> con... |
| `tools/infra/aria_scorer_lite.py` | 151 | yes | Local AriaScorer-lite semantic grounding report. AriaScorer uses Jixia + Mathlib metadata + an LLM judge. This local variant is deliberately weaker and dependency-free: it extra... |
| `tools/infra/artifacts.py` | 127 | yes | Provides artifacts tooling in tools/infra; key symbols: normalize_repo_output, load_json_dict, load_decl_index_meta, meta_matches_decl_refresh, should_skip_decl_refresh, stamp_decl_index_meta. |
| `tools/infra/autonomous_math/__init__.py` | 2 |  | Autonomous mathematician pipeline modules. |
| `tools/infra/autonomous_math/compiler_loop.py` | 33 | yes | Compiler/proof repair loop surface. |
| `tools/infra/autonomous_math/evidence_packet.py` | 167 | yes | Typed evidence packet used between research and formalization phases. |
| `tools/infra/autonomous_math/lean_coder.py` | 47 | yes | Lean coder stage. Writes a draft scaffold under reports/research/generated_lean. It does not auto-import into canonical modules. |
| `tools/infra/autonomous_math/lean_designer.py` | 64 | yes | Lean theorem-design synthesizer. |
| `tools/infra/autonomous_math/memory_ingest.py` | 26 | yes | Memory ingestion stage for autonomous_math pipeline. |
| `tools/infra/autonomous_math/pauli_auditor.py` | 57 | yes | Pauli-style admissibility audit. |
| `tools/infra/autonomous_math/research_controller.py` | 582 | yes | End-to-end autonomous mathematician controller (first production lane). |
| `tools/infra/autonomous_math/socratic_engine.py` | 40 | yes | Socratic/Jungian expansion over evidence packet. |
| `tools/infra/autonomous_math/socratic_packet.py` | 200 | yes | Packetize Socratic alchemy loop outputs into the autonomous_math evidence format. |
| `tools/infra/batch_raw_infotree_export.py` | 368 | yes | Batch RawInfoTree export with LeanDojo-style safety gates. The single-file Lean exporter is intentionally final-forest based: it runs the frontend, then walks ``commandState.inf... |
| `tools/infra/blueprint_alexandria_bridge.py` | 187 | yes | Build Blueprint-style formalization nodes from Alexandria paper artifacts. This turns semantic paper chunks into a small theorem/definition roadmap. It is not autoformalization ... |
| `tools/infra/blueprint_arango_match.py` | 117 | yes | Match Blueprint-style nodes to repo declarations and cone seeds. This is the lightweight bridge between paper-roadmap nodes and the Lean DAG owner surface. The first implementat... |
| `tools/infra/build.py` | 222 | yes | Provides build tooling in tools/infra; key symbols: log_spectral_stage, compute_olean_content_hash, compute_lean_source_hash, run_locked_lake_build, ensure_built_executable, build_indexer_command. |
| `tools/infra/build_changed_lean.py` | 156 | yes | Runs build changed Lean tooling in tools/infra; key symbols: run_git, changed_paths, path_to_module, collect_modules, parse_args, main. |
| `tools/infra/build_chiral_patch_hashes.py` | 705 | yes | Build conservative chiral patches over the declaration graph. Implements the v1.1 specification for Level 2 spectral navigation. |
| `tools/infra/build_claim_packet.py` | 54 | yes | Runs build claim packet tooling in tools/infra; key symbols: create_packet, main. |
| `tools/infra/build_link_ats_dataset.py` | 737 | yes | Runs build link ats dataset tooling in tools/infra; key symbols: DeclMeta, TypeMeta, FailurePair, PosEdge, _iter_jsonl, _stable_float_01. |
| `tools/infra/build_mcbal_library.py` | 293 | yes | Build a structured local library from downloaded mcbal blog HTML files. |
| `tools/infra/build_predigestion_packets.py` | 214 | yes | Build non-authoritative predigestion claim packets from source chunks. Predigestion packets are semantic proposal artifacts. They may guide retrieval, Hive tasks, and later form... |
| `tools/infra/build_state_first_lane.py` | 58 | yes | Runs build state first lane tooling in tools/infra; key symbols: parse_args, main. |
| `tools/infra/build_tactic_path_ranking_dataset.py` | 551 | yes | Build operator-informed tactic path ranking rows from tactic telemetry. This is the first Spectral-Journey-style dataset seam for Hive: instead of training only "next tactic" SF... |
| `tools/infra/build_tactic_training_dataset.py` | 702 | yes | Build canonical tactic SFT/DPO/failure datasets from local telemetry. This script is intentionally conservative: * SFT rows require a verified/successful transition with goal_be... |
| `tools/infra/candidate_bridge_packet.py` | 290 | yes | Candidate-bridge packet builder + validator. This is the typed contract for classifying symbolic correspondences into one of: - equivalence - obstruction - discard |
| `tools/infra/canonical_policy_lint.py` | 462 | yes | ⚖️ THE PAULI CANONICAL POLICY LINTER (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script enforces significance and structural policies on the Can... |
| `tools/infra/causal_chiral_prompt_builder.py` | 349 | yes | Runs causal chiral prompt builder tooling in tools/infra; key symbols: iter_jsonl, load_decl_index, load_expr_fingerprints, repo_path, source_excerpt, weak_cone_bfs. |
| `tools/infra/causal_cone_spectrum.py` | 1193 | yes | Causal-cone diagnostics on the SCC-condensed declaration DAG. For a given apex node, computes: - Past cone via BFS on the condensed DAG - Shell decomposition by shortest-path di... |
| `tools/infra/changed_verify.py` | 182 | yes | Runs changed verify tooling in tools/infra; key symbols: parse_args, changed_lean_files, run_file_gate, umbrella_target, main. |
| `tools/infra/check_bipartite_bleed.py` | 723 | yes | Runs check bipartite bleed tooling in tools/infra; key symbols: parse_args, load_json, ordered_unique, component_repr, sort_component_ids, parse_structure. |
| `tools/infra/check_gauge_obstruction_tags.py` | 389 | yes | Runs check gauge obstruction tags tooling in tools/infra; key symbols: DeclarationHit, parse_args, normalize_signature, split_signature_and_conclusion, classify_declaration, extract_hits. |
| `tools/infra/check_hollow_theorems.py` | 272 | yes | ⚖️ THE PAULI AUDITOR: Semantic Fidelity & Hollow Theorem Detector. "Exploration may be Jungian. Closure must be Pauli." This tool detects 'hollow' theorems that typecheck but ca... |
| `tools/infra/check_representation_depth.py` | 458 | yes | Runs check representation depth tooling in tools/infra; key symbols: parse_args, load_jsonl, normalize_decls, classify_edge, aggregate_edges, summarize. |
| `tools/infra/check_research_handoff_gate.py` | 66 | yes | ClawCode handoff gate for research-packet + NemoClaw provenance note. |
| `tools/infra/check_resident_model_endpoint.py` | 229 | yes | Check the resident local model endpoint and config alignment. This is an operational health probe only. It does not certify proof authority, model quality, or Hive promotion eli... |
| `tools/infra/check_semantic_flow_report.py` | 196 | yes | Runs check semantic flow report tooling in tools/infra; key symbols: parse_args, require, run_generate, main. |
| `tools/infra/check_vllm_mistral_compat.py` | 158 | yes | Check local vLLM CLI compatibility for Mistral-family serving. This is an operational guard for the vLLM fallback lane. It checks whether the installed `vllm serve --help` surfa... |
| `tools/infra/claim_promote.py` | 116 | yes | Phase-1 claim promotion guard. Promotes claim.status according to an allowed transition lattice. Enforces witness/formal/audit gates for formal_candidate promotion. |
| `tools/infra/classify_missing_all.py` | 185 | yes | Runs classify missing all tooling in tools/infra; key symbols: load_json, first_namespace, classify, render_md, main. |
| `tools/infra/dag_all.py` | 81 | yes | Runs DAG all tooling in tools/infra; key symbols: parse_args, step_command, main. |
| `tools/infra/dag_config.py` | 169 | yes | Provides DAG config tooling in tools/infra; key symbols: DagBuildConfig, DagAuthoritativeArtifacts, DagDerivedReports, DagCoveragePolicy, DagLeakagePolicy, DagPolicies. |
| `tools/infra/dag_doctor.py` | 472 | yes | Runs DAG doctor tooling in tools/infra; key symbols: CheckResult, parse_args, parse_iso_timestamp, format_age, file_mtime, extract_graph_coverage. |
| `tools/infra/dag_manifest.py` | 178 | yes | Runs DAG manifest tooling in tools/infra; key symbols: parse_args, _file_info, _manifest_path, _coverage_summary, main. |
| `tools/infra/dag_refresh.py` | 101 | yes | Runs DAG refresh tooling in tools/infra; key symbols: parse_args, main. |
| `tools/infra/dag_reports.py` | 113 | yes | Runs DAG reports tooling in tools/infra; key symbols: parse_args, resolve_step_command, build_report_env, main. |
| `tools/infra/dag_status.py` | 234 | yes | Runs DAG status tooling in tools/infra; key symbols: parse_args, parse_iso_timestamp, format_age, format_sync, file_mtime, extract_graph_coverage. |
| `tools/infra/debug_gravity.py` | 1168 | yes | Build Lean-grounded "gravitational" context from the proven declaration graph. The tool prefers live ArangoDB collections, but falls back to the repo's LeanTrail JSONL export. I... |
| `tools/infra/decl_graph.py` | 316 | yes | Provides decl graph tooling in tools/infra; key symbols: normalize_repo_relative, load_decl_meta, load_surface_categories, build_declaration_graph, dominant_category, build_module_graph. |
| `tools/infra/decl_graph_support.py` | 166 | yes | ⚖️ THE PAULI DECLARATION GRAPH SUPPORT Truth lives in Lean; structure lives in the graph. This module provides high-level GraphProfile objects by combining Lean source metadata ... |
| `tools/infra/deep_research/__init__.py` | 11 |  | Official-pattern deep research controller package. Modules: - clarifier: intent clarification - brief_rewriter: execution brief synthesis - planner: plan generation - retriever:... |
| `tools/infra/deep_research/brief_rewriter.py` | 102 | yes | Research-brief rewrite stage for deep research controller. |
| `tools/infra/deep_research/clarifier.py` | 83 | yes | Clarification stage for deep research controller. |
| `tools/infra/deep_research/common.py` | 63 | yes | Shared utilities for deep research controller. |
| `tools/infra/deep_research/controller.py` | 486 | yes | Official-pattern deep research controller. Implements: 1) clarifier pass 2) research-brief rewrite pass 3) planner pass 4) controlled retrieval pass 5) verifier pass 6) final sy... |
| `tools/infra/deep_research/planner.py` | 114 | yes | Planner stage for deep research controller. |
| `tools/infra/deep_research/retriever.py` | 211 | yes | Retriever/reader stage for deep research controller. |
| `tools/infra/deep_research/verifier.py` | 126 | yes | Verifier stage for deep research controller. |
| `tools/infra/deep_research/writer.py` | 55 | yes | Writer stage for deep research controller. |
| `tools/infra/dgx_spark_hybrid_orchestrator.py` | 635 | yes | Runs dgx spark hybrid orchestrator tooling in tools/infra; key symbols: StepResult, _utc_now, _utc_stamp, _resolve_profile_value, _write_text, _run_step. |
| `tools/infra/dual_hypothesis_sampler.py` | 535 | yes | Runs dual hypothesis sampler tooling in tools/infra; key symbols: ContextChunk, _utc_now, _stamp, _slug, _tokenize, _safe_read. |
| `tools/infra/enrich_tactic_path_operator_spectrum.py` | 493 | yes | Enrich tactic path-ranking rows with local operator-spectrum proxies. This pass operates on `reports/training/tactic_path_ranking.jsonl`. It does not build a global DAG matrix a... |
| `tools/infra/enrich_tactic_path_with_lightcone_spectrum.py` | 315 | yes | Attach local lightcone spectral diagnostics to tactic path-ranking rows. This is an optional enrichment pass over reports/training/tactic_path_ranking.jsonl. It consumes a bound... |
| `tools/infra/epistemic_reactor_ensemble.py` | 455 | yes | Run side-effect-free LLM ensemble infusion over a compressed cone packet. Input: info_geometry.epistemic_reactor.compressed_cone.v1 Outputs: - ensemble_samples.jsonl - ensemble_... |
| `tools/infra/export_public_release.py` | 310 | yes | Runs export public release tooling in tools/infra; key symbols: PathAudit, run, parse_excludes, gather_stats, iter_text_lines, sample_license_hits. |
| `tools/infra/external_proof_correspondence.py` | 102 | yes | Derive Lean adapter/reconstruction plans from ExternalTheoremCandidatePacket batches. This is a non-authoritative correspondence normalizer. It turns harvested foreign theorem i... |
| `tools/infra/external_theorem_harvester.py` | 520 | yes | Harvest external theorem-intelligence packets from local formal-library mirrors or arXiv. This tool deliberately emits proposal-authority `ExternalTheoremCandidatePacket`s. Fore... |
| `tools/infra/external_theorem_ingest.py` | 126 | yes | Normalize, validate, and split External Theorem Hive packet batches. Input may be JSONL or a JSON array. Each record must already be an ExternalTheoremCandidatePacket; this tool... |
| `tools/infra/extract_compressed_cone.py` | 392 | yes | Extract an SCC-compressed causal cone packet for LLM ensemble infusion. This is the "epistemic reactor" context builder: declaration -> SCC anchor -> compressed backward/forward... |
| `tools/infra/extract_expr_fingerprints.py` | 158 | yes | Build lightweight declaration-side ExprFingerprint proxies from decls.jsonl. This is a non-destructive, additive sidecar generator meant for Arango ingestion. It does NOT claim ... |
| `tools/infra/find_vacuous.py` | 66 | yes | Runs find vacuous tooling in tools/infra; key symbols: run_aql, main. |
| `tools/infra/gemini_account_adapter.py` | 162 | yes | Account-auth Gemini CLI adapter for single-segment ideation. Input: one JSON object on stdin. Output: one JSON object on stdout with creative_notes + agent status fields. No API... |
| `tools/infra/gemini_cli_guard.py` | 172 | yes | Rate-limit explicit Gemini CLI use for the theorem-factory workflow. This guard does not run Gemini. It records explicit operator-approved usage so agents do not silently poll o... |
| `tools/infra/generate_black_books_keyword_report.py` | 322 | yes | Build a full lexical index from black-book markdown files only. |
| `tools/infra/generate_black_books_story_from_keyword_index.py` | 365 | yes | Create a black-books story from full black-books keyword index. |
| `tools/infra/generate_causal_report.py` | 200 | yes | ⚖️ THE PAULI CAUSAL AUDITOR (ArangoDB SCC-Grounded) Truth lives in Lean; structure lives in the graph. This script replaces legacy networkx topological sorts with formal Causal ... |
| `tools/infra/generate_equivalence_dictionary.py` | 825 | yes | Runs generate equivalence dictionary tooling in tools/infra; key symbols: parse_args, now_utc_iso, module_name_from_path, qualify_name, push_namespace, pop_namespace. |
| `tools/infra/generate_expr_alpha_dedup.py` | 466 | yes | Runs generate expr alpha dedup tooling in tools/infra; key symbols: utc_now_iso, parse_args, iter_jsonl, parse_key, stable_hash, role_sort_key. |
| `tools/infra/generate_hypothesis_debt_report.py` | 406 | yes | Runs generate hypothesis debt report tooling in tools/infra; key symbols: DeclDebtRow, parse_args, normalize_target_path, load_targets, find_signature_end, find_top_level_colon. |
| `tools/infra/generate_keyword_research_report.py` | 373 | yes | Build a genuine full lexical index from all tracked Lean files. This script does not start from hand-picked keywords. It tokenizes every tracked `*.lean` file in the repository,... |
| `tools/infra/generate_process_flow_report.py` | 1259 | yes | Runs generate process flow report tooling in tools/infra; key symbols: parse_args, load_jsonl, validate_schema, write_jsonl, write_json, edge_use_has_value. |
| `tools/infra/generate_projection_coloring.py` | 538 | yes | Runs generate projection coloring tooling in tools/infra; key symbols: parse_args, load_json, ordered_unique, parse_module_list, safe_float, short_name. |
| `tools/infra/generate_replacement_frontier.py` | 129 | yes | ⚖️ THE PAULI REPLACEMENT FRONTIER (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script identifies 'Replacement Frontier' candidates—theorems that ... |
| `tools/infra/generate_repo_story_from_keyword_index.py` | 488 | yes | Refactor full Lean keyword indexing into a declaration-grounded repo story. Pipeline: 1) read sorted lexical index from all tracked Lean files 2) pick characteristic terms by pr... |
| `tools/infra/generate_representation_depth_graph.py` | 300 | yes | Runs generate representation depth graph tooling in tools/infra; key symbols: parse_args, build_payload, render_md, main. |
| `tools/infra/generate_semantic_flow_report.py` | 725 | yes | Runs generate semantic flow report tooling in tools/infra; key symbols: parse_args, load_jsonl, validate_schema, edge_use_has_value, edge_use_has_type, compute_transport_credit. |
| `tools/infra/generate_semantic_quotient.py` | 410 | yes | Runs generate semantic quotient tooling in tools/infra; key symbols: parse_args, load_json, parse_module_list, safe_float, build_surface_maps, theorem_shell_ratio. |
| `tools/infra/generate_sorry_equivalence.py` | 162 | yes | ⚖️ THE PAULI VACUITY STRATIFIER (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script replaces legacy heuristics with formal topological stratifica... |
| `tools/infra/generate_source_sink_compression.py` | 1364 | yes | Runs generate source sink compression tooling in tools/infra; key symbols: parse_args, short_name, load_native_structure, ordered_unique, build_native_lookup, native_component_corridor. |
| `tools/infra/generate_structural_dedup.py` | 627 | yes | Runs generate structural dedup tooling in tools/infra; key symbols: parse_args, load_json, ordered_unique, jaccard, parse_structure, component_repr. |
| `tools/infra/generate_structural_dictionary.py` | 435 | yes | Runs generate structural dictionary tooling in tools/infra; key symbols: parse_args, load_json, load_jsonl, tokenize_name, stable_hash, bucket_degree. |
| `tools/infra/generate_structural_fibers.py` | 707 | yes | Runs generate structural fibers tooling in tools/infra; key symbols: parse_args, load_json, ordered_unique, short_name, parse_structure, component_repr. |
| `tools/infra/generate_theorem_surface_index.py` | 587 | yes | Runs generate theorem surface index tooling in tools/infra; key symbols: DeclRow, parse_args, normalize_user_path, normalize_repo_relative, load_decl_rows, load_queue. |
| `tools/infra/generate_theory_cloud_movie.py` | 951 | yes | Runs generate theory cloud movie tooling in tools/infra; key symbols: NodeInfo, Snapshot, parse_args, read_json, read_jsonl, git_show_text. |
| `tools/infra/generate_theory_spire_viz.py` | 189 | yes | Generate a Spire-layered SVG visualization of the theory graph. Implements a Molecular Dynamics-style relaxation (Gradient Descent) while snapping to Spire layers. Uses meaningf... |
| `tools/infra/generate_truth_transport.py` | 83 | yes | Generate an agent-to-agent truth transport packet from Hermes artifacts. |
| `tools/infra/graph_hodge_spectrum.py` | 708 | yes | Global spectral report on the undirected shadow of the declaration DAG. Computes combinatorial Hodge invariants on the *symmetrised* dependency graph (L = D − A, undirected). Th... |
| `tools/infra/gravitational_retrieval.py` | 161 | yes | Runs gravitational retrieval tooling in tools/infra; key symbols: ArangoTarget, _http_target, run_pregel_pagerank, get_lean_source, main. |
| `tools/infra/harvest_ground_truth.py` | 102 | yes | Runs harvest ground truth tooling in tools/infra; key symbols: harvest_file, main. |
| `tools/infra/hash_signature.py` | 22 | yes | Runs hash signature tooling in tools/infra; key symbols: normalize_ws, main. |
| `tools/infra/hermes_bounded_runner.py` | 621 | yes | Run one bounded Hermes planning cycle over the research packet queue. This runner is intentionally conservative: - it polls the Hermes research packet directory - it selects one... |
| `tools/infra/hermes_isolated_adapter.py` | 261 | yes | Runs hermes isolated adapter tooling in tools/infra; key symbols: run_checked, get_directory_hash, ensure_trace_index, setup_sandbox, check_backends, exec_subagent. |
| `tools/infra/hermes_leanstral_autoproof_loop.py` | 353 | yes | Runs hermes leanstral autoproof loop tooling in tools/infra; key symbols: ProofPrompt, _lean_feedback, error_signature, recommended_next_bee, build_autoproof_trace, make_local_leanstral_proposer. |
| `tools/infra/hermes_vibe_coding_agent.py` | 293 | yes | Runs hermes vibe coding agent tooling in tools/infra; key symbols: LeanstralConfig, sha256_text, _strip_code_fence, sanitize_candidate, build_messages, openai_chat_transport. |
| `tools/infra/hive_arango_queue.py` | 2407 | yes | MotherBee queue-oriented ArangoDB manifold bootstrap for Hive agents. This tool operationalizes the queue/firewall portions of hive.md without inventing new Lean semantics. It p... |
| `tools/infra/hive_audit_worker.py` | 319 | yes | AuditBee worker for first-class Hive audit.semantic tasks. AuditBee is an authority gate, not a promotion worker. It consumes a completed BuildPacket, checks conservative semant... |
| `tools/infra/hive_bee.py` | 1563 | yes | Queue-backed autoproof bee for the live Hive manifold. This worker enforces the repo's trust boundary: - retrieve graph-grounded context from the theorem DAG on 8529 first - ask... |
| `tools/infra/hive_bee_runner.py` | 399 | yes | Bounded BeeTask runner over the local Hive packet store. This runner is deliberately small: it does not call models, Lean, Arango, or Hermes. It enforces the BeeTask/BeeResult I... |
| `tools/infra/hive_build_worker.py` | 280 | yes | BuildBee worker for first-class Hive build.verify tasks. This worker is intentionally narrow: - claims only `task_kind = "build.verify"`; - runs Lake only through `tools/infra/r... |
| `tools/infra/hive_leansearch_bee.py` | 99 | yes | LeanSearch-backed Hive proof bee lane. Alternative retrieval lane for Hive that keeps the same Lean verification/fossilization pipeline but uses LeanSearch semantic retrieval in... |
| `tools/infra/hive_leanstral_bee_worker.py` | 562 | yes | Recurrent proposal-only Leanstral bee worker. This worker is the Hive-safe version of the useful Mistral Vibe pattern: loop bounded model attempts through a verifier, keep the t... |
| `tools/infra/hive_local_packet_store.py` | 322 | yes | Append-only local JSONL store for schema-validated Hive packets. This is the first durable honeycomb cell for the Hive: a local, deterministic, Arango-free packet ledger. It val... |
| `tools/infra/hive_motherbee.py` | 680 | yes | Deterministic MotherBee scheduler v1 over the local Hive packet ledger. MotherBee v1 is intentionally a dispatcher, not a worker and not a policy firewall. It reads validated pa... |
| `tools/infra/hive_multichecker_merge.py` | 382 | yes | Merge Hive checker telemetry into one declaration-oriented report. This borrows the useful LeanDepViz idea of a unified multi-checker table while keeping this repo's trust bound... |
| `tools/infra/hive_packet_build.py` | 1365 | yes | Build Hive packets with repo-local defaults and optional schema validation. |
| `tools/infra/hive_packet_path_runner.py` | 554 | yes | Emit one real Hive packet chain from a bounded Hermes planning cycle. |
| `tools/infra/hive_packet_validate.py` | 143 | yes | Validate Hive packet JSON against repo-local machine-readable schemas. |
| `tools/infra/hive_predigestion_ingest.py` | 162 | yes | Materialize Hive queue tasks from predigested claim packets. The output tasks are intentionally non-authoritative. They ask Hive workers to map, test, formalize, or reject seman... |
| `tools/infra/hive_promotion_worker.py` | 217 | yes | PromotionBee worker for explicit Hive promotion decisions. Promotion is intentionally separate from proof, build, and audit. This worker consumes `audit.semantic` outputs and em... |
| `tools/infra/hive_qi_heartbeat.py` | 793 | yes | Convert heartbeat log pulses into Hive QI packets, lineage edges, and routed tasks. |
| `tools/infra/hive_spec_submission_policy.py` | 304 | yes | First-class Hive spec/submission lane for code-with-proof tasks. This captures the protocol from "safe and hallucination-free coding AI": * a target spec names declarations/sign... |
| `tools/infra/hive_swarm.py` | 438 | yes | Multi-role swarm worker for the live Hive queue. Roles: - generator bee: proposes a tactic from graph-grounded context - critic bee: accepts/revises/rejects the proposal before ... |
| `tools/infra/hive_workflow_policy.py` | 216 | yes | Hive workflow policy checks inspired by Lean agent workflow packs. This module is governance only. It does not prove Lean code and it does not promote packets. It gives Hive wor... |
| `tools/infra/hollow_semantic_auditor.py` | 267 | yes | ⚖️ HOLLOW SEMANTIC AUDITOR Detecting symbolic inflation and math-meaningless proofs. Protocol: "Exploration may be Jungian. Closure must be Pauli." Goal: Identify theorems that ... |
| `tools/infra/holonomy_auditor.py` | 112 | yes | Runs holonomy auditor tooling in tools/infra; key symbols: _utc_now, run_holonomy_audit, _parse_args, main. |
| `tools/infra/hydrate_arango_topology.py` | 396 | yes | Hydrate raw Arango JSONL graph exports with topology labels. This is deliberately topology-first. It does not infer semantic synonyms. It reads raw node/edge JSONL, computes gra... |
| `tools/infra/hydrated_dag_to_lean_graph.py` | 270 | yes | Project the hydrated SCC DAG into lean-graph's simple JSON schema. `patrik-cihal/lean-graph` expects a list of objects: { "name": "...", "constCategory": "Theorem\|Definition\|A... |
| `tools/infra/hypothesis_fuser_and_lean_gate.py` | 386 | yes | Runs hypothesis fuser and Lean gate tooling in tools/infra; key symbols: _utc_now, _stamp, _slug, _tokenize, _iter_jsonl, _read_goal. |
| `tools/infra/identity_protocol_metrics.py` | 172 | yes | tools/infra/identity_protocol_metrics.py Mixed-mode metric evaluator for Identity Protocol v1. - kappa can be real from structural fingerprints (dag_transport.v1) - tau_A/tau_B/... |
| `tools/infra/identity_protocol_runner.py` | 260 | yes | tools/infra/identity_protocol_runner.py Runs Identity Protocol fixtures and writes majorana identity packet artifacts. Local-first: writes artifacts only; heartbeat/queue handle... |
| `tools/infra/improver_trace_bridge.py` | 304 | yes | Normalize ImProver proof-optimization traces into diagnostic telemetry. ImProver's useful borrow is the optimization-attempt record: original proof, proposed rewrite, metric sco... |
| `tools/infra/ingest_chiral_sidecars.py` | 231 | yes | Ingest chiral sidecar JSONL artifacts into ArangoDB (immutable runs). One-command pipeline: 1) create collections/indexes if missing 2) import run/patch/spectral docs with onDup... |
| `tools/infra/ingest_hive_json.py` | 149 | yes | Extract, normalize, and persist HIVE_JSON packets emitted by HiveLogos. |
| `tools/infra/ingest_semantic_content_audit.py` | 495 | yes | Runs ingest semantic content audit tooling in tools/infra; key symbols: utc_stamp, stable_key, file_digest, read_json, iter_jsonl, write_jsonl. |
| `tools/infra/injection_build_digest.py` | 265 | yes | Build a cited literature digest markdown from an injection packet. |
| `tools/infra/injection_capture_gemini_cli.py` | 361 | yes | Capture Gemini CLI creative ideation into packet segment cards. This adapter is intentionally account-auth oriented (no API key assumptions): it shells out to a local `gemini` C... |
| `tools/infra/injection_chunk_ideate.py` | 355 | yes | Syntactically chunk packet intake text and seed per-segment ideation surfaces. This script is the earliest stage of the gemini-hermes-codex research pipeline: 1) split intake te... |
| `tools/infra/injection_common.py` | 822 | yes | Shared helpers for knowledge-injection packet tooling. |
| `tools/infra/injection_create_packet.py` | 103 | yes | Create a new knowledge injection packet. |
| `tools/infra/injection_enrich_segment.py` | 210 | yes | Update research workflow segments with creative notes and evidence. |
| `tools/infra/injection_promote.py` | 110 | yes | Promote injection claim packets between lifecycle lanes. |
| `tools/infra/injection_research_packet.py` | 183 | yes | Seed a topic-focused deep-research packet in handover/injections. |
| `tools/infra/injection_slo_report.py` | 240 | yes | Compute injection-pipeline SLO metrics and optional alert thresholds. |
| `tools/infra/injection_status.py` | 44 | yes | Show lane counts for the knowledge injection subsystem. |
| `tools/infra/jixia_batch_training.py` | 301 | yes | Run Jixia over Lean files and build local tactic-training data. Pipeline: Lean files -> Jixia raw JSON: declaration/symbol/elaboration/line -> jixia_trace_bridge.py normalized J... |
| `tools/infra/jixia_trace_bridge.py` | 339 | yes | Normalize Jixia analyzer outputs into info-geometry JSONL sidecars. Jixia emits separate JSON files for declarations, symbols, elaboration trees, and line-level proof states. Th... |
| `tools/infra/lean_auto_trace_bridge.py` | 291 | yes | Normalize lean-auto attempt traces into info-geometry diagnostic telemetry. This bridge borrows the useful seam from lean-auto without importing it as proof authority. lean-auto... |
| `tools/infra/lean_autograder_report_bridge.py` | 247 | yes | Normalize lean4-autograder-style result reports into Hive telemetry. The Robert Y. Lewis Lean 4 autograder checks named proof/definition problems and emits grading-style outcome... |
| `tools/infra/lean_interact_wrapper.py` | 227 | yes | Runs Lean interact wrapper tooling in tools/infra; key symbols: LeanProbe, _clean_lines, _build_source, run_lean_source, get_proof_state, apply_tactic. |
| `tools/infra/leandojo_probe.py` | 113 | yes | Runs leandojo probe tooling in tools/infra; key symbols: run, try_import, main. |
| `tools/infra/leandojo_to_hermes_packets.py` | 190 | yes | Runs leandojo to hermes packets tooling in tools/infra; key symbols: utc_now, slug, load_jsonl, build_packet, main. |
| `tools/infra/leandojo_token_free.py` | 133 | yes | Runs leandojo token free tooling in tools/infra; key symbols: try_import, load_sample_rows, main. |
| `tools/infra/leandojo_v2_bridge.py` | 420 | yes | Phase A bridge: normalize LeanDojo-v2 traces into IG-compatible sidecars. This bridge is intentionally read-only. It does not mutate Hive queues, Arango collections, Lean files,... |
| `tools/infra/leanparanoia_audit_bridge.py` | 230 | yes | Normalize LeanParanoia proof-soundness audits into Hive telemetry. LeanParanoia is an exploit-oriented Lean verification layer that can run checks such as sorry/metavariable/uns... |
| `tools/infra/leansearch_local.py` | 258 | yes | Dependency-free LeanSearch-style retrieval over local DAG declaration artifacts. This is not a replacement for LeanSearch. It borrows the useful shape: Lean declaration records ... |
| `tools/infra/lightcone_spectral_filter.py` | 330 | yes | Local Schur/Drazin/Hodge diagnostics for bounded causal lightcones. This script intentionally works on *bounded local slices* such as lean-graph projections or causal cone promp... |
| `tools/infra/link_scorer_common.py` | 344 | yes | Provides link scorer common tooling in tools/infra; key symbols: FeaturizerConfig, _hash_to_index_and_sign, _safe_text, _safe_float, _safe_bool, _normalize_identifier_token. |
| `tools/infra/llm_thermo_conformance.py` | 550 | yes | Numerical conformance checks for LLM thermo/operator identities. This script audits runtime trace rows against the finite owner lane identities: - softmax simplex normalization ... |
| `tools/infra/logipedia_markdown_distill.py` | 495 | yes | Distill `docs/Logipedia.md`-style theorem-bank transcripts into Hive packets. The distiller is deliberately pre-authority. It classifies claims and performs a read-only owner au... |
| `tools/infra/materialize_lossless_infotree.py` | 490 | yes | Materialize a topology-preserving raw DAG graph for ArangoDB. This builds a layered graph, not a replacement projection: * raw layer: every declaration endpoint and every raw de... |
| `tools/infra/millennium_problem_bridge.py` | 199 | yes | Build local retrieval records for LeanMillenniumPrizeProblems. The LeanMillenniumPrizeProblems repo is a statement corpus, not a solution corpus. This bridge indexes its problem... |
| `tools/infra/module_keyword_theory_program.py` | 666 | yes | Runs module keyword theory program tooling in tools/infra; key symbols: PathHit, rel, split_camel, decl_belongs_to_module, extract_keywords, iter_scan_files. |
| `tools/infra/openai_deep_research_datasource_mcp_example.py` | 97 | yes | Minimal search/fetch MCP datasource for OpenAI Deep Research. This file is a template for the *nested* MCP server used by deep-research jobs. It is not the Codex-facing gateway.... |
| `tools/infra/openai_deep_research_gateway.py` | 590 | yes | Codex-facing MCP gateway for OpenAI Deep Research. Architecture: 1) Codex-facing MCP tools (`dr_start`, `dr_status`, `dr_result`, ...) 2) Deep-research execution via OpenAI Resp... |
| `tools/infra/paperproof_bidirectional_cone.py` | 300 | yes | Join proof forests with Arango causal cone packets. This builds a two-sided proof-geometry artifact: backward owner/dependency cone glued through declarations/files/references l... |
| `tools/infra/paperproof_jixia_compare.py` | 261 | yes | Compare Paperproof-style proof packets with Jixia tactic transitions. This is an audit tool for proof-state extraction quality. It treats both Paperproof-style packets and Jixia... |
| `tools/infra/paperproof_proof_forest.py` | 282 | yes | Build proof-forest graphs from Paperproof-style trace packets. Paperproof's key modeling insight is that goal evolution is naturally a tree, while hypothesis evolution is better... |
| `tools/infra/paperproof_rpc_export_schema.py` | 190 | yes | Normalize Paperproof RPC/webview proof trees into local trace packets. Paperproof's Lean side returns a proof tree shaped like: [ { "tacticString": "...", "goalBefore": {"type":... |
| `tools/infra/paperproof_tableau_detector.py` | 177 | yes | Detect semantic-tableau-like proof strategy in Paperproof traces. Paperproof's semantic-tableaux analogy is operationally useful: by_contra / contradiction entry -> negated goal... |
| `tools/infra/paperproof_trace_bridge.py` | 271 | yes | Render proof-state telemetry as Paperproof-style proof-history packets. This is a lightweight bridge inspired by Paperproof's proof visualization model: hypotheses, goals, tacti... |
| `tools/infra/paperproof_training_effects.py` | 147 | yes | Label tactic effects from Paperproof-style proof-history packets. The labels are intentionally conservative and heuristic. They are training features for local LLM/reranker work... |
| `tools/infra/pauli_authority_bridge.py` | 194 | yes | ⚖️ THE PAULI AUTHORITY BRIDGE Truth lives in Lean; structure lives in the graph. This module is the sole source of structural truth for the reporting suite. It implements the 'C... |
| `tools/infra/pda_forml4_bridge.py` | 233 | yes | Normalize PDA/FormL4-style autoformalization records into IG sidecars. This bridge is intentionally read-only. PDA/FormL4 records are useful as natural-language/formal-statement... |
| `tools/infra/plot_decl_graph.py` | 435 | yes | Runs plot decl graph tooling in tools/infra; key symbols: parse_args, plot_module_graph, write_hotspot_json, render_burndown_markdown, write_burndown_reports, write_summary. |
| `tools/infra/prima_materia_ingest.py` | 126 | yes | Phase-1 Prima Materia ingest (ArangoDB). Inputs: - artifact JSON file (required) - optional claims JSON file (list of claim docs) Writes: - prima_materia_artifacts - claims (sta... |
| `tools/infra/real_prover_trace_bridge.py` | 249 | yes | Normalize REAL-Prover traces into info-geometry training telemetry. REAL-Prover is a retrieval-augmented stepwise prover. Its result payloads carry proof-search nodes, generator... |
| `tools/infra/refresh_blueprint_tags.py` | 420 | yes | Runs refresh blueprint tags tooling in tools/infra; key symbols: parse_args, normalize_user_path, load_decl_rows, is_generated_or_unstable_name, prefix_match, module_to_path. |
| `tools/infra/refresh_decl_graph.py` | 209 | yes | Runs refresh decl graph tooling in tools/infra; key symbols: parse_args, main. |
| `tools/infra/report_rep_layers.py` | 82 | yes | Report L0-L5 representation-layer counts and cross-layer raw edges. |
| `tools/infra/reports/__init__.py` | 0 |  | Package initializer for tools/infra/reports. |
| `tools/infra/reports/classify_markdown_corpus.py` | 427 | yes | Runs classify markdown corpus tooling in tools/infra; key symbols: parse_args, tracked_files, untracked_files, is_markdown, command_line_count, heading_count. |
| `tools/infra/reports/common.py` | 45 |  | Provides common tooling in tools/infra; key symbols: normalize_user_path, load_json, read_text, write_text, relpath, generated_timestamp. |
| `tools/infra/reports/generate_bilingual_spine_report.py` | 479 | yes | Runs generate bilingual spine report tooling in tools/infra; key symbols: ModuleAudit, parse_args, module_to_path, parse_imports, extract_module_docstring, declaration_docstring_gaps. |
| `tools/infra/reports/generate_bridge_candidates.py` | 280 | yes | Runs generate bridge candidates tooling in tools/infra; key symbols: parse_args, safe_slug, decl_tail, infer_transport_shape, risk_from_row, display_source_file. |
| `tools/infra/reports/generate_bridge_thinness_index.py` | 147 | yes | Runs generate bridge thinness index tooling in tools/infra; key symbols: Finding, priority_for, is_target, trim_proof, classify_block, collect_findings. |
| `tools/infra/reports/generate_debt_candidates.py` | 406 | yes | Runs generate debt candidates tooling in tools/infra; key symbols: DebtSignal, DebtTarget, parse_args, file_bucket, normalize_name, parse_queue. |
| `tools/infra/reports/generate_llm_debt_prompts.py` | 202 | yes | Runs generate LLM debt prompts tooling in tools/infra; key symbols: parse_args, render_creative, render_critical, main. |
| `tools/infra/reports/generate_llm_frontier_prompts.py` | 188 | yes | Runs generate LLM frontier prompts tooling in tools/infra; key symbols: parse_args, render_creative, render_critical, main. |
| `tools/infra/reports/generate_markdown_hygiene_report.py` | 430 | yes | Runs generate markdown hygiene report tooling in tools/infra; key symbols: parse_args, load_json, to_rel, normalize_title, iter_markdown_links, resolve_link_target. |
| `tools/infra/reports/generate_repository_surface_index.py` | 269 | yes | Runs generate repository surface index tooling in tools/infra; key symbols: parse_args, tracked_files, untracked_files, is_config_path, top_level_bucket, extension_bucket. |
| `tools/infra/reports/generate_self_optimization_report.py` | 99 | yes | Runs generate self optimization report tooling in tools/infra; key symbols: frontier_names, render_report, main. |
| `tools/infra/reports/generate_surrogate_index.py` | 455 | yes | Runs generate surrogate index tooling in tools/infra; key symbols: Decl, Finding, module_to_relpath, is_comment_line, file_bucket, priority_for. |
| `tools/infra/reports/generate_unification_index.py` | 412 | yes | Runs generate unification index tooling in tools/infra; key symbols: ModuleEntry, UnificationEntry, parse_args, status_explainer, render_md, main. |
| `tools/infra/reports/generate_vacuity_index.py` | 109 | yes | Runs generate vacuity index tooling in tools/infra; key symbols: Finding, parse_args, active_priority, collect_findings, render_md, main. |
| `tools/infra/representation_depth_from_graph.py` | 262 | yes | Derive representation-depth rows from materialized graph artifacts. This is the fast query/report path for the L0-L5 layer contract. Lean remains the source of the `@[rep_depth ... |
| `tools/infra/representation_depth_io.py` | 197 | yes | Provides representation depth io tooling in tools/infra; key symbols: load_json, rel_repo_path, interval_label, load_depth_index, module_to_rel_file, inferred_file_kind. |
| `tools/infra/rerank_arango_links.py` | 588 | yes | Runs rerank Arango links tooling in tools/infra; key symbols: ArangoTarget, _utc_now, _safe_text, _safe_int, _iter_jsonl, _load_model. |
| `tools/infra/research_controller.py` | 581 | yes | Closed-loop repo research controller. Implements a practical planner -> retriever -> reader -> critic -> memory loop using existing repository tooling. This is intentionally ope... |
| `tools/infra/research_digest_worker.py` | 197 | yes | Runs research digest worker tooling in tools/infra; key symbols: parse_args, sanitize, shell, extract_ids, build_run_dir, import_event. |
| `tools/infra/research_packet.py` | 336 | yes | Research packet builder + validator. This script defines the typed handoff contract from Hermes deep-research intake to Prompt A / Prompt B routing. |
| `tools/infra/residue_quarantine.py` | 85 | yes | Runs residue quarantine tooling in tools/infra; key symbols: absorb_failure, main. |
| `tools/infra/rethlas_verification_bridge.py` | 169 | yes | Normalize Rethlas verification reports into local audit telemetry. Rethlas verifies natural-language markdown proof blueprints with a strict JSON contract. This bridge preserves... |
| `tools/infra/run_copilot_codex_lean_pipeline.py` | 170 | yes | Runs run copilot codex Lean pipeline tooling in tools/infra; key symbols: utc_now, build_codex_prompt, build_pipeline_payload, write_json, run_pipeline, parse_args. |
| `tools/infra/run_full_dag_toolchain.py` | 251 | yes | Runs run full DAG toolchain tooling in tools/infra; key symbols: run_step, process_exists, preflight_build_lock_health, main. |
| `tools/infra/run_locked_lake_build.py` | 45 | yes | Runs run locked lake build tooling in tools/infra; key symbols: parse_args, main. |
| `tools/infra/run_predigestion_to_hive_demo.py` | 161 | yes | Run a reproducible predigestion-to-Hive dry run. This is an operational smoke/demo lane: it builds advisory predigestion claim packets, materializes non-authoritative Hive queue... |
| `tools/infra/run_proof_prompt_batch.py` | 258 | yes | Runs run proof prompt batch tooling in tools/infra; key symbols: utc_now, backend_defaults, extract_completion_text, assess_output_quality, build_result_payload, write_json. |
| `tools/infra/run_socratic_alchemy_batch.py` | 70 | yes | Batch runner for Socratic alchemy loops over multiple seed prompt files. |
| `tools/infra/run_socratic_alchemy_loop.py` | 1029 | yes | Run a guarded Gemini -> Codex -> guarded Gemini Socratic alchemy loop. Features: - N conceptual Gemini/Codex rounds - Codex Lean4 hypothesis generation - N compile/repair cycles... |
| `tools/infra/safeverify_audit_bridge.py` | 257 | yes | Normalize SafeVerify target/submission verification into Hive telemetry. SafeVerify compares compiled target/submission `.olean` files and checks that submitted declarations imp... |
| `tools/infra/scan_third_party_licenses.py` | 292 | yes | Runs scan third party licenses tooling in tools/infra; key symbols: Hit, FileFinding, run, load_owner_names, load_excluded_prefixes, is_text_file. |
| `tools/infra/score_link_candidates.py` | 123 | yes | Runs score link candidates tooling in tools/infra; key symbols: _iter_jsonl, _load_model, parse_args, main. |
| `tools/infra/select_openclaw_target.py` | 335 | yes | Runs select openclaw target tooling in tools/infra; key symbols: parse_args, load_json_file, seed_for_row, slugify, make_structural_commands, make_uncovered_debt_commands. |
| `tools/infra/semantic_audit.py` | 228 | yes | Runs semantic audit tooling in tools/infra; key symbols: normalize_ws, sha256_text, extract_decl_signature, get_current_imports, get_repo_root, get_git_file. |
| `tools/infra/shadow_plant_worker.py` | 407 | yes | Epistemic Reactor: gated shadow planting worker. This is the first mutating phase of the epistemic reactor. It consumes an ensemble consensus packet and plants the result into a... |
| `tools/infra/socratic_packet_to_sampler_jsonl.py` | 135 | yes | Convert a Socratic packet into sampler-style JSONL rows for hypothesis_fuser_and_lean_gate. |
| `tools/infra/timings.py` | 176 | yes | Provides timings tooling in tools/infra; key symbols: indexer_timing_log_path, indexer_timing_json_path, report_timing_json_path, parse_indexer_timing_log, build_indexer_timing_payload, write_indexer_timing_sidecar. |
| `tools/infra/trace_and_retrieve.py` | 104 | yes | Runs trace and retrieve tooling in tools/infra; key symbols: get_git_sha, get_cache_path, build_index, retrieve, main. |
| `tools/infra/train_link_scorer.py` | 297 | yes | Runs train link scorer tooling in tools/infra; key symbols: Example, _iter_jsonl, _to_examples, _predict_probs, _eval_split, parse_args. |
| `tools/infra/ulam_trace_bridge.py` | 158 | yes | Normalize UlamAI run.jsonl traces into info-geometry tactic telemetry. UlamAI traces contain proof-state/tactic transitions produced by a search and repair loop. This bridge pre... |
| `tools/infra/validate_raw_infotree_export.py` | 486 | yes | Validate the stage-1 raw InfoTree export contract. This checks topology preservation surfaces, not mathematical truth. It ensures that an export directory contains the required ... |
| `tools/infra/verify_layered_arango_descent.py` | 166 | yes | Verify raw-to-overlay-to-raw descent in the layered Arango graph. |
| `tools/infra/verify_raw_infotree_arango_descent.py` | 517 | yes | Verify raw_infotree_* descent invariants in ArangoDB. This verifier is intentionally non-mutating. It checks that the stage ``raw_infotree_*`` projection imported by ``arango_ra... |
| `tools/infra/visualize_causal_chiral_cone_packet.py` | 342 | yes | Render a causal/chiral cone prompt packet as a small offline HTML view. Input is the JSON emitted by: tools/infra/arango_causal_chiral_cone_prompt.py This viewer is intentionall... |
| `tools/lean4-skills/analyze_let_usage.py` | 372 | yes | Analyze let binding usage to detect false-positive optimization candidates. Helps avoid the #1 pitfall: inlining let bindings that are used multiple times, which actually INCREA... |
| `tools/lean4-skills/find_exact_candidates.py` | 262 | yes | Find proof blocks that are good candidates for `exact?` replacement. Scans Lean 4 files for short tactic proofs (2-8 lines) where replacing the entire proof body with `exact?` m... |
| `tools/lean4-skills/find_golfable.py` | 699 | yes | Find proof-golfing opportunities in Lean 4 files. Identifies optimization patterns with estimated reduction potential. |
| `tools/lean4-skills/minimize_imports.py` | 259 | yes | minimize_imports.py - Remove unused imports from Lean 4 files Usage: ./minimize_imports.py <file> [--dry-run] [--verbose] This script identifies and removes unused imports by: 1... |
| `tools/lean4-skills/parse_command_args.py` | 92 | yes | Standalone CLI for the lean4 slash-command parser. Usage: python3 parse_command_args.py <command> [--cwd PATH] -- <raw tail> Exit codes: 0 — success (prints ParseResult JSON to ... |
| `tools/lean4-skills/parse_lean_errors.py` | 221 | yes | Parse Lean compiler errors into structured JSON for repair routing. Output schema: { "errorHash": "type_mismatch_42", "errorType": "type_mismatch", "message": "type mismatch at.... |
| `tools/lean4-skills/solver_cascade.py` | 153 | yes | Try automated solvers in sequence before resampling with LLM. Handles 40-60% of simple cases mechanically. Cascade order: 1. rfl (definitional equality) 2. simp (simplifier) 3. ... |
| `tools/lean4-skills/sorry_analyzer.py` | 490 | yes | sorry_analyzer.py - Extract and analyze sorry statements in Lean 4 code Usage: ./sorry_analyzer.py <file-or-directory> [--format=FORMAT \| --format FORMAT] [--interactive] [--in... |
| `tools/lean4-skills/test_apply_exact_chains.py` | 97 | yes | Fixture tests for find_apply_exact_chains() in find_golfable.py. Run from the repo root: python3 plugins/lean4/lib/scripts/test_apply_exact_chains.py |
| `tools/lean4-skills/try_exact_at_step.py` | 370 | yes | Try `exact?` at various points in Lean 4 proofs to find one-liner replacements. For each candidate proof block, replaces the tactic body with `exact?`, swaps the source file wit... |
| `tools/lean_improver_probe.py` | 201 | yes | ImProver-style proof optimization probe for local Lean modules. This is deliberately non-mutating. It borrows ImProver's first optimization idea, "rank proofs by a metric before... |
| `tools/leantrail/__init__.py` | 1 |  | LeanTrail tooling package. |
| `tools/leantrail/adapters.py` | 530 | yes | Provides adapters tooling in tools/leantrail; key symbols: load_snapshot, save_snapshot, _json_text, _parse_json_text, _iter_jsonl, _stable_key. |
| `tools/leantrail/arango_ingest.py` | 151 | yes | Runs Arango ingest tooling in tools/leantrail; key symbols: ArangoTarget, _ensure_collections, _read_text, _http_target, _import_jsonl, _collection_count. |
| `tools/leantrail/arango_physics_evaluator.py` | 549 | yes | Runs Arango physics evaluator tooling in tools/leantrail; key symbols: PhysicsWeights, ArangoTarget, _utc_now, _safe_float, _snapshot_from_path, _local_eval. |
| `tools/leantrail/conformance.py` | 696 | yes | Runs conformance tooling in tools/leantrail; key symbols: PathQuery, _utc_now, _read_snapshot, _jaccard, _pct_drift, _top_ids. |
| `tools/leantrail/export.py` | 86 | yes | Runs export tooling in tools/leantrail; key symbols: _parse_args, main. |
| `tools/leantrail/failure_harvester.py` | 471 | yes | Runs failure harvester tooling in tools/leantrail; key symbols: _utc_now, _utc_iso, _iter_jsonl, _norm_file, _load_decl_index, _closest_decl. |
| `tools/leantrail/hole_packets.py` | 477 | yes | Runs hole packets tooling in tools/leantrail; key symbols: HoleAccumulator, _utc_now, _iter_jsonl, _stable_hole_id, _load_required_lock_status, _build_holes. |
| `tools/leantrail/path_lock_registry.py` | 236 | yes | Runs path lock registry tooling in tools/leantrail; key symbols: _utc_now, _snapshot_from_path, _path_id, _load_registry, _row_fingerprint, _write_registry. |
| `tools/pathing.py` | 131 | yes | Provides pathing tooling in tools/root; key symbols: repo_root, lean_root, resolve_existing, default_src_root, default_docs_map_root, default_artifacts_root. |
| `tools/planner/__init__.py` | 1 |  | Planner package for vacuity matching, normalization, ranking, and reporting. |
| `tools/planner/admissibility.py` | 293 |  | Strict admissibility precheck scaffold logic. |
| `tools/planner/common.py` | 467 |  | Shared planner types, constants, and helpers. |
| `tools/planner/matching.py` | 576 |  | Planner matching context and declaration resolution logic. |
| `tools/planner/normalization.py` | 574 |  | Bridge observation normalization and signal extraction. |
| `tools/planner/policy.py` | 47 |  | Planner policy constants and calibration helpers. |
| `tools/planner/ranking.py` | 812 |  | Ranking logic for vacuity, owner, replacement, corridor, and declaration plans. |
| `tools/planner/report.py` | 187 |  | Markdown and JSON report rendering for vacuity planner outputs. |
| `tools/plot_decl_graph.py` | 10 | yes | Runs plot decl graph tooling in tools/root; key symbols: module-level logic. |
| `tools/proof_driver.py` | 157 | yes | Runs proof driver tooling in tools/root; key symbols: parse_args, load_json, placeholder_reasons, selected_sketch, insert_before_namespace_end, materialize_signature. |
| `tools/quality/__init__.py` | 0 |  | Package initializer for tools/quality. |
| `tools/quality/audit_constructivity.py` | 395 | yes | Runs audit constructivity tooling in tools/quality; key symbols: Finding, rel, module_to_path, read_quarantine_manifest, quarantined_paths, iter_files. |
| `tools/quality/audit_docstrings.py` | 88 | yes | Runs audit docstrings tooling in tools/quality; key symbols: audit_file, run_audit. |
| `tools/quality/audit_naming.py` | 100 | yes | Runs audit naming tooling in tools/quality; key symbols: is_snake_case, is_upper_camel_case, is_lower_camel_case, audit_file, run_audit. |
| `tools/quality/audit_semantic.py` | 733 | yes | Runs audit semantic tooling in tools/quality; key symbols: InterfaceInfo, rel, module_to_path, line_of, path_to_module, strip_lean_comments. |
| `tools/quality/audit_style.py` | 85 | yes | Runs audit style tooling in tools/quality; key symbols: audit_file, run_audit. |
| `tools/quality/check_closure_debt_gate.py` | 142 | yes | Runs check closure debt gate tooling in tools/quality; key symbols: parse_args, load_json, tokenize_count, collect_group_modules, main. |
| `tools/quality/check_equivalence_dictionary_gate.py` | 131 | yes | Runs check equivalence dictionary gate tooling in tools/quality; key symbols: parse_args, load_json, compute_report_metrics, main. |
| `tools/quality/check_frontier_integrity_gate.py` | 221 | yes | Hard integrity gate for closure/spectral/sinkhorn frontier clusters. Enforced conditions on configured frontier files: - no `sorry` / `admit` - no `axiom` declarations - no `pos... |
| `tools/quality/check_translation_registry.py` | 127 | yes | Runs check translation registry tooling in tools/quality; key symbols: parse_args, read_registry_rows, anchor_in_registry, anchor_declared, main. |
| `tools/quality/closure_ast_validator.py` | 46 | yes | Closure AST Validator: Ensures only allowed Lean AST node types are present in closure modules. Requires: ast_export (Lean 4), Python 3.8+ |
| `tools/quality/closure_debt_auditor.py` | 198 | yes | Closure Debt Auditor: Identifies unanchored Lean declarations, theory islands, and holes in the dependency graph. UPGRADED: Uses ArangoDB Authority Bridge for zero-false-positiv... |
| `tools/quality/common.py` | 43 |  | Provides common tooling in tools/quality; key symbols: resolve_target_dir, iter_lean_files, print_grouped_violations. |
| `tools/quality/detect_hollow_theorems.py` | 50 | yes | Hollow Theorem Detector for Lean Codebases Flags theorems/defs as :hollow if: - The conclusion is already known from strictly weaker data - The main bridge is assumed, not prove... |
| `tools/quality/detect_ornamental_hypotheses.py` | 42 | yes | Ornamental Hypothesis Detector for Lean Codebases Flags theorems/defs as :ornamental if: - The main domain object appears only in the assumptions, not in the proof body - There ... |
| `tools/quality/dvorak_audit.py` | 61 | yes | Runs dvorak audit tooling in tools/quality; key symbols: audit_file, main. |
| `tools/quality/functorial_invariance_audit.py` | 402 | yes | Runs functorial invariance audit tooling in tools/quality; key symbols: Corridor, rel, load_jsonl, has_rep_depth, parse_args, load_rep_tagged_names. |
| `tools/quality/kanban_evidence_lint.py` | 582 | yes | Runs kanban evidence lint tooling in tools/quality; key symbols: Finding, rel, load_json_or_jsonl, normalize_payload, nonempty, produced. |
| `tools/quality/mathfulness_audit.py` | 414 | yes | Unified mathfulness audit for info-geometry-lean declarations. This gate is intentionally conservative: * Lean/DAG declaration presence is kernel/provenance evidence, not semant... |
| `tools/quality/pauli_seal_audit.py` | 667 | yes | Runs pauli seal audit tooling in tools/quality; key symbols: Finding, rel, strip_comments, count_density, line_of, declaration_header. |
| `tools/quality/semantic_content_audit.py` | 736 | yes | Runs semantic content audit tooling in tools/quality; key symbols: ModuleAudit, rel, module_name, module_to_path, read_manifest, in_scope. |
| `tools/refresh_blueprint_tags.py` | 10 | yes | Runs refresh blueprint tags tooling in tools/root; key symbols: module-level logic. |
| `tools/refresh_decl_graph.py` | 10 | yes | Runs refresh decl graph tooling in tools/root; key symbols: module-level logic. |
| `tools/run_locked_lake_build.py` | 10 | yes | Runs run locked lake build tooling in tools/root; key symbols: module-level logic. |
| `tools/run_optimization_cycle.py` | 1401 | yes | Runs run optimization cycle tooling in tools/root; key symbols: CommandResult, CandidateSketch, HydrationResult, ProofAttemptRecord, acquire_worktree_lock, release_worktree_lock. |
| `tools/select_openclaw_target.py` | 10 | yes | Runs select openclaw target tooling in tools/root; key symbols: module-level logic. |
| `tools/semantic_block_export.py` | 10 | yes | Runs semantic block export tooling in tools/root; key symbols: module-level logic. |
| `tools/skynet_v2.py` | 10 | yes | Runs skynet v2 tooling in tools/root; key symbols: module-level logic. |
| `tools/theorem_significance.py` | 544 | yes | ⚖️ THE PAULI SIGNIFICANCE AUDITOR (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script replaces legacy lexical heuristics with formal topological ... |
| `tools/update_repo_docs.py` | 10 | yes | Runs update repo docs tooling in tools/root; key symbols: module-level logic. |
| `tools/vacuity_planner.py` | 409 | yes | Planning-only vacuity planner orchestrator. This tool aggregates read-only compiler bridge payloads, vacuity reports, dependency metadata, and ownership metadata to produce rank... |
| `tools/vacuity_policy_config.py` | 71 | yes | Shared vacuity policy configuration for Layer B and Layer C. This module is the single source of truth for: - strict path prefixes - bridge file hints - attribute-based exemptio... |
