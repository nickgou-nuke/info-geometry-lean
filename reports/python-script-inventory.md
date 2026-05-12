# Python Script Inventory

Generated from current checkout using `git ls-files` plus untracked non-ignored `*.py` files.

Scope excludes `.lake/`, virtualenvs, `external/`, `external_refs/`, `artifacts/`, and `archive/`. External donor trees are intentionally excluded from the repository-owned script count.

- Scoped Python files: `668`
- Total scoped Python lines: `141920`
- AST/syntax failures: `0`
- Files with CLI/entrypoint signals: `422`

## Directory breakdown

- `tools`: `367` files
- `tests`: `227` files
- `src`: `28` files
- `scripts`: `19` files
- `leantrail`: `12` files
- `.scripts_archive`: `3` files
- `jsonschema`: `3` files
- `jsonschema_shadow`: `3` files
- `cli`: `2` files
- `lean`: `1` files
- `presentation`: `1` files
- `scratch`: `1` files
- `skills`: `1` files

## `.scripts_archive`

### `.scripts_archive/bulk_namespace_rewrite.py`

- Lines: `173`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, re`
- Top-level functions: `path_to_namespace, find_first_namespace, has_declarations, insertion_index_after_header, classify, apply_rewrite, main`
- What it does: Defines path_to_namespace, find_first_namespace, has_declarations, insertion_index_after_header, classify

### `.scripts_archive/gather_cluster_code.py`

- Lines: `49`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `json, pathlib, sys, tools`
- Top-level functions: `main`
- What it does: Defines main

### `.scripts_archive/namespace_patch_plan.py`

- Lines: `68`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, pathlib, re`
- Top-level functions: `suggested_namespace, main`
- What it does: Defines suggested_namespace, main

## `cli`

### `cli/__init__.py`

- Lines: `2`
- AST status: `ok`
- What it does: Command entrypoints for local InfoGeometry tooling.

### `cli/igf.py`

- Lines: `18`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, igf, pathlib, sys`
- What it does: Compatibility wrapper for the package-local igf CLI.

## `jsonschema`

### `jsonschema/__init__.py`

- Lines: `224`
- AST status: `ok`
- Imports: `__future__, collections, dataclasses, datetime, exceptions, typing`
- Classes: `Draft202012Validator, FormatChecker, RefResolver`
- Top-level functions: `_looks_like_ref, _iter_errors, validate`
- What it does: Defines Draft202012Validator, FormatChecker, RefResolver, _looks_like_ref, _iter_errors, validate

### `jsonschema/exceptions.py`

- Lines: `12`
- AST status: `ok`
- Imports: `__future__`
- Classes: `ValidationError`
- What it does: Defines ValidationError

### `jsonschema/validators.py`

- Lines: `7`
- AST status: `ok`
- Imports: `__future__`
- Top-level functions: `validator_for`
- What it does: Defines validator_for

## `jsonschema_shadow`

### `jsonschema_shadow/__init__.py`

- Lines: `205`
- AST status: `ok`
- Imports: `__future__, collections, dataclasses, datetime, exceptions, typing`
- Classes: `Draft202012Validator, FormatChecker, RefResolver`
- Top-level functions: `_looks_like_ref, _iter_errors, validate`
- What it does: Defines Draft202012Validator, FormatChecker, RefResolver, _looks_like_ref, _iter_errors, validate

### `jsonschema_shadow/exceptions.py`

- Lines: `12`
- AST status: `ok`
- Imports: `__future__`
- Classes: `ValidationError`
- What it does: Defines ValidationError

### `jsonschema_shadow/validators.py`

- Lines: `7`
- AST status: `ok`
- Imports: `__future__`
- Top-level functions: `validator_for`
- What it does: Defines validator_for

## `lean`

### `lean/DAG/ingest.py`

- Lines: `75`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, mgclient`
- Top-level functions: `ingest`
- What it does: Defines ingest

## `leantrail`

### `leantrail/__init__.py`

- Lines: `3`
- AST status: `ok`
- What it does: LeanTrail package.

### `leantrail/api/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: HTTP API surfaces for LeanTrail.

### `leantrail/api/server.py`

- Lines: `210`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, argparse`
- Imports: `__future__, argparse, http, json, leantrail, pathlib, typing, urllib`
- Classes: `LeanTrailRequestHandler`
- Top-level functions: `_bool_query, _parse_args, main`
- What it does: Defines LeanTrailRequestHandler, _bool_query, _parse_args, main

### `leantrail/backend/__init__.py`

- Lines: `3`
- AST status: `ok`
- What it does: Backend services for LeanTrail.

### `leantrail/backend/app.py`

- Lines: `12`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, leantrail`
- What it does: Compatibility entrypoint for LeanTrail API.

### `leantrail/backend/extractor.py`

- Lines: `17`
- AST status: `ok`
- Imports: `__future__, pathlib, subprocess`
- Top-level functions: `run_refresh_pipeline`
- What it does: Defines run_refresh_pipeline

### `leantrail/backend/indexer.py`

- Lines: `314`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, argparse`
- Imports: `__future__, argparse, collections, extractor, json, models, normalizer, pathlib, subprocess, typing`
- Top-level functions: `_run_git_lines, _safe_git_head, _iter_jsonl, _module_from_lean_path, _detect_changed_modules, _collect_decl_to_module, _compute_impacted_modules, _edge_key, _merge_incremental_snapshot, build_snapshot, _parse_args, main`
- What it does: Defines _run_git_lines, _safe_git_head, _iter_jsonl, _module_from_lean_path, _detect_changed_modules

### `leantrail/backend/models.py`

- Lines: `78`
- AST status: `ok`
- Imports: `__future__, dataclasses, typing`
- Classes: `NodeRecord, EdgeRecord, GraphSnapshot`
- What it does: Defines NodeRecord, EdgeRecord, GraphSnapshot

### `leantrail/backend/normalizer.py`

- Lines: `468`
- AST status: `ok`
- Imports: `__future__, datetime, json, models, pathlib, subprocess, typing`
- Classes: `LeanTrailNormalizer`
- Top-level functions: `_utc_now, _read_json, _iter_jsonl, _edge_key, _load_failed_transition_index, _load_path_lock_index, _default_path_state, _annotate_edge_path_states, _annotate_node_endpoints, _safe_git_head, _read_toolchain, _module_family, _infer_role, _is_lawful_depth`
- What it does: Defines LeanTrailNormalizer, _utc_now, _read_json, _iter_jsonl, _edge_key, _load_failed_transition_index

### `leantrail/backend/query_api.py`

- Lines: `206`
- AST status: `ok`
- Imports: `__future__, datetime, indexer, json, jsonschema, models, pathlib, re, rpc_adapter, store, tools, typing`
- Classes: `LeanTrailQueryAPI`
- Top-level functions: `_utc_now, _slug`
- What it does: Defines LeanTrailQueryAPI, _utc_now, _slug

### `leantrail/backend/rpc_adapter.py`

- Lines: `25`
- AST status: `ok`
- Imports: `__future__, pathlib, typing`
- Classes: `LeanRPCAdapter`
- What it does: Defines LeanRPCAdapter

### `leantrail/backend/store.py`

- Lines: `257`
- AST status: `ok`
- Imports: `__future__, collections, models, typing`
- Classes: `GraphStore`
- What it does: Defines GraphStore

## `presentation`

### `presentation/gen_figures.py`

- Lines: `240`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `matplotlib, numpy, os, pathlib`
- Top-level functions: `_style, _save, gen_kl_divergence, gen_fisher_information, gen_entropy_manifold, _count_lean_files, gen_module_coverage, gen_bridge_map, gen_transformer_pipeline, gen_ricci_bridge, main`
- What it does: Defines _style, _save, gen_kl_divergence, gen_fisher_information, gen_entropy_manifold

## `scratch`

### `scratch/test_arango_authority.py`

- Lines: `16`
- AST status: `ok`
- Imports: `os, pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

## `scripts`

### `scripts/__init__.py`

- Lines: `28`
- AST status: `ok`
- Imports: `__future__, analysis, docs`
- What it does: Top-level Python package for active InfoGeometry scripting helpers.

### `scripts/__main__.py`

- Lines: `4`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `cli`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `scripts/analysis/filter_project_decls.py`

- Lines: `100`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, re, scripts, tools, typing`
- Top-level functions: `collect_declared_namespaces, prefix_match, main`
- What it does: Defines collect_declared_namespaces, prefix_match, main

### `scripts/analysis/lean/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `scripts/analysis/lean/catastrophe_surface.py`

- Lines: `176`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, numpy, pathlib, sys`
- Top-level functions: `build_dataset, free_energy_surface, parse_args, main`
- What it does: Render finite-temperature free-energy catastrophe surfaces.

### `scripts/analysis/utils.py`

- Lines: `31`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, json, pathlib, re, typing`
- Top-level functions: `load_json, dump_json, prefix_match, sanitize_label_suffix, matches_prefix`
- What it does: Defines load_json, dump_json, prefix_match, sanitize_label_suffix, matches_prefix

### `scripts/cli.py`

- Lines: `48`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, sys, typing`
- Top-level functions: `main`
- What it does: Defines main

### `scripts/docs/build_doc_map.py`

- Lines: `215`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, pathlib, scripts, tools, typing`
- Top-level functions: `decls_payload_to_list, index_decls, resolve_node, build_resolved, main`
- What it does: Defines decls_payload_to_list, index_decls, resolve_node, build_resolved, main

### `scripts/docs/convert/__init__.py`

- Lines: `2`
- AST status: `ok`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `scripts/docs/convert/common.py`

- Lines: `171`
- AST status: `ok`
- Imports: `json, loguru, pydantic, re, subprocess, sys, typing`
- Classes: `BaseSchema, NodePart, FormattingConfig, Node, Position, DeclarationRange, DeclarationLocation, NodeWithPos`
- Top-level functions: `_quote, _indent, _wrap, _wrap_list, make_docstring`
- What it does: Defines BaseSchema, NodePart, FormattingConfig, _quote, _indent, _wrap

### `scripts/docs/convert/main.py`

- Lines: `169`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, argparse`
- Imports: `argparse, common, json, loguru, modify_latex, modify_lean, os, parse_latex, pathlib, subprocess, sys`
- Top-level functions: `main`
- What it does: Defines main

### `scripts/docs/convert/modify_latex.py`

- Lines: `65`
- AST status: `ok`
- Imports: `common, loguru, parse_latex, pathlib, re`
- Top-level functions: `write_latex_source`
- What it does: Defines write_latex_source

### `scripts/docs/convert/modify_lean.py`

- Lines: `267`
- AST status: `ok`
- Imports: `common, loguru, pathlib, re, typing`
- Top-level functions: `split_declaration, insert_attributes, modify_source, add_lean_architect_import, topological_sort, write_blueprint_attributes`
- What it does: Utilities for adding @[blueprint] attributes to Lean source files.

### `scripts/docs/convert/parse_latex.py`

- Lines: `308`
- AST status: `ok`
- Imports: `common, dataclasses, loguru, pathlib, pydantic, re, typing, uuid`
- Classes: `SourceInfo, LatexSource`
- Top-level functions: `read_latex_file, find_and_remove_command, find_and_remove_command_arguments, find_and_remove_command_argument, strip_empty_lines, remove_bracketed_prefix, parse_and_remove_blueprint_commands, try_int, generate_new_lean_name, parse_nodes, get_bibliography_files`
- What it does: Defines SourceInfo, LatexSource, read_latex_file, find_and_remove_command, find_and_remove_command_arguments, find_and_remove_command_argument

### `scripts/docs/emit_markdown_index.py`

- Lines: `96`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, scripts, tools, typing`
- Top-level functions: `main`
- What it does: Defines main

### `scripts/docs/gen_content_auto_tex_from_header.py`

- Lines: `30`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, pathlib, tools`
- Top-level functions: `extract_blueprint_nodes, main`
- What it does: Defines extract_blueprint_nodes, main

### `scripts/docs/proof_gap_report.py`

- Lines: `211`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, pathlib, re`
- Classes: `Decl, Gap`
- Top-level functions: `escape_tex, natlang, collect_gaps, render_md, render_tex, main`
- What it does: Generate a proof-gap report (sorry/axiom) in Markdown and LaTeX.

### `scripts/intake/parser.py`

- Lines: `71`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, os, re`
- Classes: `LegacyIntakeParser`
- What it does: Defines LegacyIntakeParser

### `scripts/utils.py`

- Lines: `1`
- AST status: `ok`
- Imports: `analysis`
- What it does: Script/module with top-level Python statements; inspect before operational use.

## `skills`

### `skills/chatgpt-history-to-hermes/scripts/chatgpt_history_migrate.py`

- Lines: `211`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, datetime, json, pathlib, re`
- Top-level functions: `safe_text, normalize_role, extract_messages, md_escape, build_memory_candidates, write_jsonl, main`
- What it does: Defines safe_text, normalize_role, extract_messages, md_escape, build_memory_candidates

## `src`

### `src/igf/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: igf greenfield kernel package.

### `src/igf/artifacts/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Artifact utilities for igf.

### `src/igf/artifacts/compatibility_adapters.py`

- Lines: `153`
- AST status: `ok`
- Imports: `__future__, hashlib, igf, json, pathlib, typing`
- Top-level functions: `_load_jsonl, _write_jsonl, normalize_run_id, stable_key, _infer_run_id_from_patch_from, normalize_artifacts`
- What it does: Defines _load_jsonl, _write_jsonl, normalize_run_id, stable_key, _infer_run_id_from_patch_from

### `src/igf/artifacts/io.py`

- Lines: `61`
- AST status: `ok`
- Imports: `__future__, hashlib, json, pathlib, typing`
- Top-level functions: `sha256_file, sha256_optional_file, read_jsonl, write_json, count_jsonl_rows, file_hashes`
- What it does: Defines sha256_file, sha256_optional_file, read_jsonl, write_json, count_jsonl_rows

### `src/igf/artifacts/manifest.py`

- Lines: `67`
- AST status: `ok`
- Imports: `__future__, igf, pathlib, time, typing`
- Top-level functions: `build_manifest, write_manifest`
- What it does: Defines build_manifest, write_manifest

### `src/igf/cli.py`

- Lines: `225`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, igf, json, pathlib, sys`
- Top-level functions: `_add_build_args, main`
- What it does: Canonical igf CLI package entrypoint.

### `src/igf/config/__init__.py`

- Lines: `33`
- AST status: `ok`
- Imports: `igf`
- What it does: Configuration utilities for igf.

### `src/igf/config/env_aliases.py`

- Lines: `114`
- AST status: `ok`
- Imports: `__future__, os, pathlib, re, typing`
- Top-level functions: `repo_root_from, _strip_env_value, load_repo_arango_env, get_env_alias, normalized_arango_env, first_present_name, arango_endpoint, arango_database, arango_username, arango_password`
- What it does: Defines repo_root_from, _strip_env_value, load_repo_arango_env, get_env_alias, normalized_arango_env

### `src/igf/config/loader.py`

- Lines: `17`
- AST status: `ok`
- Imports: `__future__, igf, pathlib`
- Top-level functions: `load_arango_config`
- What it does: Defines load_arango_config

### `src/igf/config/model.py`

- Lines: `11`
- AST status: `ok`
- Imports: `__future__, dataclasses`
- Classes: `ArangoConfig`
- What it does: Defines ArangoConfig

### `src/igf/config/preflight.py`

- Lines: `54`
- AST status: `ok`
- Imports: `__future__, igf, json`
- Top-level functions: `run_preflight, print_preflight_json`
- What it does: Defines run_preflight, print_preflight_json

### `src/igf/graph/__init__.py`

- Lines: `45`
- AST status: `ok`
- Imports: `igf`
- What it does: Arango graph registry and query helpers for igf.

### `src/igf/graph/arango_client.py`

- Lines: `44`
- AST status: `ok`
- Imports: `__future__, collections, igf, indexes, typing`
- Top-level functions: `connect_db, ensure_collections_and_indexes`
- What it does: Defines connect_db, ensure_collections_and_indexes

### `src/igf/graph/arango_http.py`

- Lines: `213`
- AST status: `ok`
- Imports: `__future__, base64, dataclasses, igf, json, typing, urllib`
- Classes: `ArangoHttpTarget`
- Top-level functions: `target_from_config, auth_header, db_url, sys_url, request_json, request_raw, ensure_database, list_collections, create_collection, truncate_collection, drop_collection, collection_count, ensure_index, import_jsonl, execute_aql`
- What it does: Defines ArangoHttpTarget, target_from_config, auth_header, db_url, sys_url, request_json

### `src/igf/graph/collections.py`

- Lines: `15`
- AST status: `ok`
- Imports: `__future__`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `src/igf/graph/indexes.py`

- Lines: `26`
- AST status: `ok`
- Imports: `__future__`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `src/igf/graph/query_registry.py`

- Lines: `246`
- AST status: `ok`
- Imports: `__future__, dataclasses, typing`
- Classes: `QuerySpec`
- Top-level functions: `get_query`
- What it does: Canonical AQL query registry for igf greenfield kernel.

### `src/igf/graph/query_runner.py`

- Lines: `20`
- AST status: `ok`
- Imports: `__future__, query_registry, typing`
- Top-level functions: `run_query, resolve_run_id`
- What it does: Defines run_query, resolve_run_id

### `src/igf/pipeline/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Pipeline stages for igf.

### `src/igf/pipeline/build.py`

- Lines: `137`
- AST status: `ok`
- Imports: `__future__, igf, json, pathlib, subprocess, sys, typing`
- Top-level functions: `_repo_root, _parse_summary, resolve_graph_inputs, build_chiral_patches`
- What it does: Defines _repo_root, _parse_summary, resolve_graph_inputs, build_chiral_patches

### `src/igf/pipeline/candidates.py`

- Lines: `88`
- AST status: `ok`
- Imports: `__future__, igf, typing`
- Top-level functions: `find_maxent_style_patch_candidates, find_log_barrier_patch_candidates`
- What it does: Defines find_maxent_style_patch_candidates, find_log_barrier_patch_candidates

### `src/igf/pipeline/ingest.py`

- Lines: `46`
- AST status: `ok`
- Imports: `__future__, igf, pathlib, typing`
- Top-level functions: `_upsert_document, ingest_artifacts`
- What it does: Defines _upsert_document, ingest_artifacts

### `src/igf/pipeline/orchestrator.py`

- Lines: `91`
- AST status: `ok`
- Imports: `__future__, igf, pathlib, typing`
- Top-level functions: `run_offline_pipeline`
- What it does: Defines run_offline_pipeline

### `src/igf/pipeline/report.py`

- Lines: `19`
- AST status: `ok`
- Imports: `__future__, igf, pathlib, typing`
- Top-level functions: `report_artifacts`
- What it does: Defines report_artifacts

### `src/igf/pipeline/validate.py`

- Lines: `108`
- AST status: `ok`
- Imports: `__future__, igf, json, jsonschema, pathlib, typing`
- Top-level functions: `_load_schema, validate_artifacts`
- What it does: Defines _load_schema, validate_artifacts

### `src/igf/pipeline/verify.py`

- Lines: `34`
- AST status: `ok`
- Imports: `__future__, igf, typing`
- Top-level functions: `verify_run`
- What it does: Defines verify_run

### `src/igf/policy/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Claim-safety policy helpers for igf.

### `src/igf/policy/claim_scope.py`

- Lines: `38`
- AST status: `ok`
- Imports: `__future__`
- Top-level functions: `apply_default_claim_policy, validate_claim_policy`
- What it does: Defines apply_default_claim_policy, validate_claim_policy

## `tests`

### `tests/alexandria/test_automathtext_arango_ingest.py`

- Lines: `101`
- AST status: `ok`
- Imports: `__future__, json, pathlib, pytest, tools`
- Top-level functions: `_jsonl, test_build_import_plan_classifies_automath_collections, test_dry_run_writes_report_without_network, test_require_all_rejects_partial_graph, test_edge_endpoint_validation_is_strict, test_batched_jsonl_keeps_import_payloads_bounded`
- What it does: Defines _jsonl, test_build_import_plan_classifies_automath_collections, test_dry_run_writes_report_without_network, test_require_all_rejects_partial_graph, test_edge_endpoint_validation_is_strict

### `tests/alexandria/test_automathtext_v2_ingest.py`

- Lines: `331`
- AST status: `ok`
- Imports: `__future__, gzip, json, pathlib, tools`
- Top-level functions: `_jsonl, _read_jsonl, test_automathtext_ingest_emits_triples_and_debruijn_edges, test_automathtext_ingest_preserves_raw_authority_boundary, test_automathtext_ingest_deep_dag_rows_have_chain_of_custody, test_automathtext_sharded_ingest_writes_bounded_retrieval_only_shards, test_automathtext_filtered_gzip_shards_keep_operator_theorem_rows, test_automathtext_ingest_emits_alexandria_ranker_interface`
- What it does: Defines _jsonl, _read_jsonl, test_automathtext_ingest_emits_triples_and_debruijn_edges, test_automathtext_ingest_preserves_raw_authority_boundary, test_automathtext_ingest_deep_dag_rows_have_chain_of_custody

### `tests/alexandria/test_conductive_context_to_lean_skeleton.py`

- Lines: `50`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys`
- Top-level functions: `test_conductive_context_to_lean_skeleton_generates_review_packet`
- What it does: Defines test_conductive_context_to_lean_skeleton_generates_review_packet

### `tests/alexandria/test_download_automathtext_v2.py`

- Lines: `41`
- AST status: `ok`
- CLI/entrypoint signals: `argparse`
- Imports: `__future__, argparse, pytest, tools`
- Top-level functions: `test_pattern_for_config_supports_quality_buckets, test_full_mode_requires_explicit_allow_full, test_make_plan_default_operator_configs`
- What it does: Defines test_pattern_for_config_supports_quality_buckets, test_full_mode_requires_explicit_allow_full, test_make_plan_default_operator_configs

### `tests/alexandria/test_fetch_arxiv_corpus.py`

- Lines: `63`
- AST status: `ok`
- Imports: `tools`
- Top-level functions: `test_tex_to_text_preserves_theorem_equation_and_labels, test_tex_to_text_strips_figure_tikz_scaffolding`
- What it does: Defines test_tex_to_text_preserves_theorem_equation_and_labels, test_tex_to_text_strips_figure_tikz_scaffolding

### `tests/alexandria/test_graph_context_rank.py`

- Lines: `99`
- AST status: `ok`
- Imports: `__future__, networkx, tools`
- Top-level functions: `test_conductive_debruijn_edges_gain_query_aligned_weight, test_coarse_components_group_connected_context_by_entities, test_scc_quotient_scores_distribute_component_score_to_cycle_members`
- What it does: Defines test_conductive_debruijn_edges_gain_query_aligned_weight, test_coarse_components_group_connected_context_by_entities, test_scc_quotient_scores_distribute_component_score_to_cycle_members

### `tests/alexandria/test_materialize_coarse_scc_overlay.py`

- Lines: `53`
- AST status: `ok`
- Imports: `__future__, json, pathlib, tools`
- Top-level functions: `write_jsonl, read_jsonl, test_materialize_coarse_scc_overlay_preserves_member_descent`
- What it does: Defines write_jsonl, read_jsonl, test_materialize_coarse_scc_overlay_preserves_member_descent

### `tests/alexandria/test_proof_synthesis_report.py`

- Lines: `63`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys`
- Top-level functions: `test_proof_synthesis_report_renders_authority_bounded_prompt`
- What it does: Defines test_proof_synthesis_report_renders_authority_bounded_prompt

### `tests/alexandria/test_repair_lineage.py`

- Lines: `161`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys, tools`
- Top-level functions: `broken_chunk, test_repair_lineage_marks_purified_node_as_active_replacement, test_repair_lineage_failure_preserves_broken_node_without_purified_successor, test_repair_lineage_cli_appends_attempt_and_purified_chunk`
- What it does: Defines broken_chunk, test_repair_lineage_marks_purified_node_as_active_replacement, test_repair_lineage_failure_preserves_broken_node_without_purified_successor, test_repair_lineage_cli_appends_attempt_and_purified_chunk

### `tests/alexandria/test_retrieve_context.py`

- Lines: `102`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys`
- Top-level functions: `write_jsonl, test_retrieve_context_includes_source_and_score_breakdown`
- What it does: Defines write_jsonl, test_retrieve_context_includes_source_and_score_breakdown

### `tests/alexandria/test_semantic_ingest.py`

- Lines: `22`
- AST status: `ok`
- Imports: `pathlib, tools`
- Top-level functions: `test_digest_document_extracts_sections_chunks_and_entities`
- What it does: Defines test_digest_document_extracts_sections_chunks_and_entities

### `tests/alexandria/test_verify_automathtext_arango_descent.py`

- Lines: `87`
- AST status: `ok`
- Imports: `__future__, tools, typing`
- Top-level functions: `_count_runner, test_run_checks_accepts_closed_automath_graph, test_run_checks_requires_raw_descent_collections_nonempty, test_run_checks_reports_structural_orphan_failure, test_run_checks_reports_missing_theorem_shape_descent`
- What it does: Defines _count_runner, test_run_checks_accepts_closed_automath_graph, test_run_checks_requires_raw_descent_collections_nonempty, test_run_checks_reports_structural_orphan_failure, test_run_checks_reports_missing_theorem_shape_descent

### `tests/infra/test_build_chiral_patch_hashes.py`

- Lines: `204`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `write_jsonl, read_jsonl, test_build_chiral_patch_hashes_emits_three_patch_families`
- What it does: Defines write_jsonl, read_jsonl, test_build_chiral_patch_hashes_emits_three_patch_families

### `tests/infra/test_dag_pipeline.py`

- Lines: `113`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `run_script, assert_valid_empty_json, test_process_flow_report_allows_missing_inputs, test_process_flow_report_fails_without_allow_missing_input, test_semantic_flow_report_allows_missing_inputs, test_semantic_flow_check_allows_missing_report, test_semantic_flow_check_fails_without_allow_missing_input`
- What it does: Defines run_script, assert_valid_empty_json, test_process_flow_report_allows_missing_inputs, test_process_flow_report_fails_without_allow_missing_input, test_semantic_flow_report_allows_missing_inputs

### `tests/infra/test_env_stability.py`

- Lines: `15`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, tools, unittest`
- Classes: `TestEnvCompaction`
- What it does: Defines TestEnvCompaction

### `tests/infra/test_igf_build_manifest.py`

- Lines: `98`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `write_jsonl, test_igf_build_writes_manifest_with_hashes_and_counts`
- What it does: Defines write_jsonl, test_igf_build_writes_manifest_with_hashes_and_counts

### `tests/infra/test_igf_cli_run_smoke.py`

- Lines: `37`
- AST status: `ok`
- Imports: `pathlib, shutil, subprocess, sys`
- Top-level functions: `test_cli_run_help_lists_new_flags, test_cli_run_rejects_invalid_verify_limit_type`
- What it does: Defines test_cli_run_help_lists_new_flags, test_cli_run_rejects_invalid_verify_limit_type

### `tests/infra/test_igf_greenfield_suite.py`

- Lines: `464`
- AST status: `ok`
- Imports: `json, pathlib, pytest, shutil, subprocess, sys`
- Classes: `FakeHttpResponse`
- Top-level functions: `write_jsonl, read_jsonl, make_minimal_artifacts, test_validate_strict_passes_on_minimal_greenfield_fixture, test_validate_strict_fails_when_member_run_id_missing, test_validate_strict_accepts_patch_run_id_legacy_alias, test_validate_strict_rejects_formal_authority_without_proof_link, test_normalize_backfills_member_and_edge_fields, test_run_id_normalization_and_stable_keys_are_deterministic, test_query_registry_has_required_queries, test_arango_http_execute_aql_follows_cursor, test_arango_http_collection_helpers_build_expected_requests, test_log_barrier_candidates_pipeline_is_routing_only, test_maxent_candidate_pipeline_uses_safe_query, test_preflight_reports_missing_credentials`
- What it does: Defines FakeHttpResponse, write_jsonl, read_jsonl, make_minimal_artifacts, test_validate_strict_passes_on_minimal_greenfield_fixture, test_validate_strict_fails_when_member_run_id_missing

### `tests/infra/test_igf_ingest_cli_contract.py`

- Lines: `59`
- AST status: `ok`
- Imports: `igf, json, pathlib, sys, types`
- Classes: `_StubDB`
- Top-level functions: `_invoke_ingest, test_ingest_cli_success_exit_0, test_ingest_cli_failure_exit_1`
- What it does: Defines _StubDB, _invoke_ingest, test_ingest_cli_success_exit_0, test_ingest_cli_failure_exit_1

### `tests/infra/test_igf_orchestrator_run.py`

- Lines: `82`
- AST status: `ok`
- Imports: `igf, pathlib, sys`
- Top-level functions: `test_run_offline_pipeline_returns_exit_1_on_build_failure, test_run_offline_pipeline_returns_exit_2_on_verify_verdict_failure, test_run_offline_pipeline_full_success_exit_0`
- What it does: Defines test_run_offline_pipeline_returns_exit_1_on_build_failure, test_run_offline_pipeline_returns_exit_2_on_verify_verdict_failure, test_run_offline_pipeline_full_success_exit_0

### `tests/infra/test_igf_run_cli_contract.py`

- Lines: `59`
- AST status: `ok`
- Imports: `igf, json, pathlib, sys, types`
- Top-level functions: `_run_with_stubbed_orchestrator, test_igf_run_cli_returns_0_on_success, test_igf_run_cli_returns_1_on_runtime_failure, test_igf_run_cli_returns_2_on_verify_verdict_failure`
- What it does: Defines _run_with_stubbed_orchestrator, test_igf_run_cli_returns_0_on_success, test_igf_run_cli_returns_1_on_runtime_failure, test_igf_run_cli_returns_2_on_verify_verdict_failure

### `tests/infra/test_igf_run_json_surface.py`

- Lines: `120`
- AST status: `ok`
- Imports: `igf, json, pathlib, sys, types`
- Top-level functions: `_invoke_run, test_run_json_surface_build_failure_has_minimal_keys, test_run_json_surface_validate_failure_has_build_and_validate, test_run_json_surface_verify_failure_has_all_stages, test_run_json_surface_success_with_verify_has_all_stages`
- What it does: Defines _invoke_run, test_run_json_surface_build_failure_has_minimal_keys, test_run_json_surface_validate_failure_has_build_and_validate, test_run_json_surface_verify_failure_has_all_stages, test_run_json_surface_success_with_verify_has_all_stages

### `tests/infra/test_igf_verify_cli_contract.py`

- Lines: `129`
- AST status: `ok`
- Imports: `igf, json, pathlib, sys, types`
- Classes: `_StubDB`
- Top-level functions: `_invoke_verify, test_verify_cli_success_exit_0_with_required_fields, test_verify_cli_verdict_failure_exit_2, test_verify_cli_passes_limit_argument`
- What it does: Defines _StubDB, _invoke_verify, test_verify_cli_success_exit_0_with_required_fields, test_verify_cli_verdict_failure_exit_2, test_verify_cli_passes_limit_argument

### `tests/test_aesop_tactic_prior.py`

- Lines: `36`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_tactic_head_handles_common_prefixes, test_classify_tactic_uses_aesop_style_phases, test_aesop_tactic_prior_cli_single_tactic`
- What it does: Defines test_tactic_head_handles_common_prefixes, test_classify_tactic_uses_aesop_style_phases, test_aesop_tactic_prior_cli_single_tactic

### `tests/test_analyze_stall_distributions.py`

- Lines: `88`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_write_jsonl, test_analyze_stalls_aggregates_distribution, test_analyze_stalls_cli`
- What it does: Defines _write_jsonl, test_analyze_stalls_aggregates_distribution, test_analyze_stalls_cli

### `tests/test_analyze_tactic_path_ranking.py`

- Lines: `104`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_write_jsonl, _ranking_row, test_analyze_tactic_path_ranking_reports_distribution_and_baseline, test_analyze_tactic_path_ranking_handles_empty_input, test_analyze_tactic_path_ranking_cli`
- What it does: Defines _write_jsonl, _ranking_row, test_analyze_tactic_path_ranking_reports_distribution_and_baseline, test_analyze_tactic_path_ranking_handles_empty_input, test_analyze_tactic_path_ranking_cli

### `tests/test_arango_dag_algorithms.py`

- Lines: `77`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `tools, unittest`
- Classes: `TestArangoDagAlgorithms`
- What it does: Defines TestArangoDagAlgorithms

### `tests/test_arango_env_wrappers.py`

- Lines: `84`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `TestArangoEnvWrappers`
- What it does: Defines TestArangoEnvWrappers

### `tests/test_arango_gravity_context.py`

- Lines: `518`
- AST status: `ok`
- Imports: `importlib, json, os, pathlib, subprocess, sys`
- Top-level functions: `load_tool_module, write_jsonl, test_gravity_context_loads_repo_arango_env_aliases, test_igf_config_and_legacy_arango_env_resolve_same_config, test_gravity_context_ranks_proven_neighbor_and_excerpt, test_gravity_context_uses_equivalence_dictionary_to_expand_query, test_gravity_context_can_filter_by_rep_layer, test_gravity_context_uses_spectral_edge_priors_without_promotion`
- What it does: Defines load_tool_module, write_jsonl, test_gravity_context_loads_repo_arango_env_aliases, test_igf_config_and_legacy_arango_env_resolve_same_config, test_gravity_context_ranks_proven_neighbor_and_excerpt

### `tests/test_arango_raw_infotree_ingest.py`

- Lines: `116`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `write_jsonl, test_raw_infotree_edges_preserve_projection_descent`
- What it does: Defines write_jsonl, test_raw_infotree_edges_preserve_projection_descent

### `tests/test_aria_concept_graph.py`

- Lines: `116`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_write_records, test_extract_concepts_is_deterministic_and_bounded, test_build_concept_graph_grounds_with_leansearch_records, test_aria_concept_graph_cli_writes_packet`
- What it does: Defines _write_records, test_extract_concepts_is_deterministic_and_bounded, test_build_concept_graph_grounds_with_leansearch_records, test_aria_concept_graph_cli_writes_packet

### `tests/test_aria_scorer_lite.py`

- Lines: `87`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_write_records, test_extract_lean_identifiers_skips_keywords, test_score_alignment_exact_grounds_identifier, test_aria_scorer_lite_cli_writes_report`
- What it does: Defines _write_records, test_extract_lean_identifiers_skips_keywords, test_score_alignment_exact_grounds_identifier, test_aria_scorer_lite_cli_writes_report

### `tests/test_audit_constructivity.py`

- Lines: `55`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `importlib, pathlib, sys, tempfile, types, unittest`
- Classes: `AuditConstructivityTests`
- Top-level functions: `_load_audit_module`
- What it does: Defines AuditConstructivityTests, _load_audit_module

### `tests/test_blueprint_borrowed_tools.py`

- Lines: `122`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `_jsonl, test_blueprint_alexandria_bridge_builds_nodes_with_candidates, test_blueprint_arango_match_recommends_apex_from_local_records, test_paperproof_training_effects_labels_tactic_steps`
- What it does: Defines _jsonl, test_blueprint_alexandria_bridge_builds_nodes_with_candidates, test_blueprint_arango_match_recommends_apex_from_local_records, test_paperproof_training_effects_labels_tactic_steps

### `tests/test_bohm_equilibrium_seed_bridge.py`

- Lines: `25`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_bohm_stationary_k_split_uses_equilibrium_seed_theorem`
- What it does: Defines test_bohm_stationary_k_split_uses_equilibrium_seed_theorem

### `tests/test_bohm_stateqgt_equilibrium_seed_bridge.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_bohm_stateqgt_stationary_uses_equilibrium_seed_theorem`
- What it does: Defines test_bohm_stateqgt_stationary_uses_equilibrium_seed_theorem

### `tests/test_build_tactic_path_ranking_dataset.py`

- Lines: `186`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_write_jsonl, test_tactic_path_ranking_groups_success_and_failure_candidates, test_tactic_path_ranking_marks_stalls_as_negative_one, test_tactic_path_ranking_cli`
- What it does: Defines _write_jsonl, test_tactic_path_ranking_groups_success_and_failure_candidates, test_tactic_path_ranking_marks_stalls_as_negative_one, test_tactic_path_ranking_cli

### `tests/test_build_tactic_training_dataset.py`

- Lines: `263`
- AST status: `ok`
- CLI/entrypoint signals: `argparse`
- Imports: `argparse, json, pathlib, tools`
- Top-level functions: `_write_jsonl, _args, test_normalize_goal_hash_is_whitespace_stable, test_build_tactic_training_dataset_emits_sft_and_failures, test_build_tactic_training_dataset_pairs_dpo_by_same_theorem_and_goal_hash, test_build_tactic_training_dataset_ingests_real_prover_traces, test_build_tactic_training_dataset_ingests_jixia_tactic_transitions, test_build_tactic_training_dataset_filters_jixia_aggregate_tactics`
- What it does: Defines _write_jsonl, _args, test_normalize_goal_hash_is_whitespace_stable, test_build_tactic_training_dataset_emits_sft_and_failures, test_build_tactic_training_dataset_pairs_dpo_by_same_theorem_and_goal_hash

### `tests/test_canonical_drazin_singular_star_adapter.py`

- Lines: `48`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_singular_drazin_star_roots_exist, test_canonical_star_transport_is_adapter_over_singular_root, test_canonical_selfadjoint_star_uses_singular_selfadjoint_root`
- What it does: Defines decl_block, test_singular_drazin_star_roots_exist, test_canonical_star_transport_is_adapter_over_singular_root, test_canonical_selfadjoint_star_uses_singular_selfadjoint_root

### `tests/test_canonical_moore_penrose_singular_unique_adapter.py`

- Lines: `44`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_singular_moore_penrose_unique_root_exists, test_canonical_moore_penrose_unique_is_singular_adapter`
- What it does: Defines decl_block, test_singular_moore_penrose_unique_root_exists, test_canonical_moore_penrose_unique_is_singular_adapter

### `tests/test_canonical_policy_lint.py`

- Lines: `26`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `tools, unittest`
- Classes: `CanonicalPolicyLintHelpersTests`
- What it does: Defines CanonicalPolicyLintHelpersTests

### `tests/test_cartan_kkt_projector_root_chain.py`

- Lines: `39`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_cartan_projector_idempotence_uses_named_expansion_roots, test_kkt_projector_idempotence_consumes_cartan_projector_roots`
- What it does: Defines decl_block, test_cartan_projector_idempotence_uses_named_expansion_roots, test_kkt_projector_idempotence_consumes_cartan_projector_roots

### `tests/test_causal_chiral_prompt_builder.py`

- Lines: `38`
- AST status: `ok`
- Imports: `tools`
- Top-level functions: `test_weak_cone_uses_dependency_and_reverse_edges, test_expr_context_is_honest_when_unavailable, test_expr_context_marks_fingerprint_as_diagnostic_proxy`
- What it does: Defines test_weak_cone_uses_dependency_and_reverse_edges, test_expr_context_is_honest_when_unavailable, test_expr_context_marks_fingerprint_as_diagnostic_proxy

### `tests/test_causal_cone_spectrum.py`

- Lines: `320`
- AST status: `ok`
- Imports: `causal_cone_spectrum, pathlib, pytest, sys`
- Top-level functions: `mock_dag, mock_tags, sig_cache, own_parity_cache, test_past_cone_bfs, test_forward_cone_bfs, test_shell_decomposition, test_component_signature, test_component_own_parities, test_component_signature_no_deps, test_precompute_signatures, test_find_binding_witnesses, test_binding_witnesses_require_coherence, test_declaration_mass, test_declaration_mass_leaf, test_binding_mass, test_binding_mass_mixed_predecessor, test_find_boundary_nodes`
- What it does: Tests for tools/infra/causal_cone_spectrum.py against a synthetic mock DAG.

### `tests/test_check_resident_model_endpoint.py`

- Lines: `92`
- AST status: `ok`
- Imports: `http, json, pathlib, threading, tools`
- Classes: `Handler`
- Top-level functions: `start_server, test_run_check_passes_against_mock_endpoint, test_run_check_detects_config_mismatch`
- What it does: Defines Handler, start_server, test_run_check_passes_against_mock_endpoint, test_run_check_detects_config_mismatch

### `tests/test_check_vacuity_policy.py`

- Lines: `93`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `importlib, json, pathlib, tempfile, types, typing, unittest`
- Classes: `CheckVacuityPolicyTests`
- Top-level functions: `_load_gate_module`
- What it does: Defines CheckVacuityPolicyTests, _load_gate_module

### `tests/test_check_vllm_mistral_compat.py`

- Lines: `54`
- AST status: `ok`
- Imports: `json, pathlib, stat, tools`
- Top-level functions: `make_fake_vllm, test_check_compat_passes_when_required_flags_exist, test_check_compat_fails_when_required_flags_missing, test_check_compat_reports_vllm_source_markers`
- What it does: Defines make_fake_vllm, test_check_compat_passes_when_required_flags_exist, test_check_compat_fails_when_required_flags_missing, test_check_compat_reports_vllm_source_markers

### `tests/test_chiral_lightcone_algebra_witness.py`

- Lines: `29`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_chiral_lightcone_algebra_witness_is_theorem_backed, test_chiral_lightcone_packet_does_not_claim_global_partition_positivity`
- What it does: Defines test_chiral_lightcone_algebra_witness_is_theorem_backed, test_chiral_lightcone_packet_does_not_claim_global_partition_positivity

### `tests/test_cik_drazin_star_selfadjoint_root_chain.py`

- Lines: `75`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_drazin_star_transport_root_uses_star_equations_and_uniqueness, test_certified_inverse_kernel_derives_had_from_ha_not_as_hypothesis, test_inverse_kernel_algebra_complement_uses_base_selfadjoint_only, test_cik_projector_star_projection_adapters_are_lean_rooted`
- What it does: Defines decl_block, test_drazin_star_transport_root_uses_star_equations_and_uniqueness, test_certified_inverse_kernel_derives_had_from_ha_not_as_hypothesis, test_inverse_kernel_algebra_complement_uses_base_selfadjoint_only, test_cik_projector_star_projection_adapters_are_lean_rooted

### `tests/test_cik_selfadjoint_idempotent_constructor.py`

- Lines: `57`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_of_selfadjoint_idempotent_constructor_uses_real_roots, test_of_selfadjoint_idempotent_exposes_base_selfadjoint_hA, test_of_selfadjoint_idempotent_derives_had_from_hA_path, test_of_selfadjoint_idempotent_projector_star_uses_hA_only`
- What it does: Defines decl_block, test_of_selfadjoint_idempotent_constructor_uses_real_roots, test_of_selfadjoint_idempotent_exposes_base_selfadjoint_hA, test_of_selfadjoint_idempotent_derives_had_from_hA_path, test_of_selfadjoint_idempotent_projector_star_uses_hA_only

### `tests/test_clnn_corridor.py`

- Lines: `112`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `ClNNCorridorTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines ClNNCorridorTests, _run_snippet, _combined_output

### `tests/test_clnn_specialization_and_metric.py`

- Lines: `110`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `ClNNSpecializationAndMetricTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines ClNNSpecializationAndMetricTests, _run_snippet, _combined_output

### `tests/test_closed_range_moore_penrose_existence.py`

- Lines: `68`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_closed_range_mp_existence_uses_restricted_inverse_not_finite_dimension, test_closed_range_mp_existence_returns_penrose_and_projector_identities, test_cik_closed_range_readbacks_use_closed_range_existence_and_uniqueness`
- What it does: Defines decl_block, test_closed_range_mp_existence_uses_restricted_inverse_not_finite_dimension, test_closed_range_mp_existence_returns_penrose_and_projector_identities, test_cik_closed_range_readbacks_use_closed_range_existence_and_uniqueness

### `tests/test_compiler_bridge_rpc.py`

- Lines: `237`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `contextlib, pathlib, sys, tempfile, tools, unittest`
- Classes: `CompilerBridgeRpcTests`
- What it does: Defines CompilerBridgeRpcTests

### `tests/test_conformal_anomaly_projector_commute_iff.py`

- Lines: `25`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, re, unittest`
- Classes: `ConformalAnomalyProjectorCommuteIffTests`
- Top-level functions: `has_decl`
- What it does: Defines ConformalAnomalyProjectorCommuteIffTests, has_decl

### `tests/test_conformal_fisher_square_response_bridge.py`

- Lines: `16`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_conformal_fisher_square_response_constructs_nonnegativity`
- What it does: Defines test_conformal_fisher_square_response_constructs_nonnegativity

### `tests/test_conformal_operator_admissibility_witness.py`

- Lines: `16`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_conformal_operator_admissibility_has_constructive_partition_witness`
- What it does: Defines test_conformal_operator_admissibility_has_constructive_partition_witness

### `tests/test_conformal_projector_agreement.py`

- Lines: `70`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `ConformalProjectorAgreementTests`
- Top-level functions: `has_decl`
- What it does: Defines ConformalProjectorAgreementTests, has_decl

### `tests/test_coordinateless_souriau_kms_cyclic_branch.py`

- Lines: `29`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_cyclic_constructive_branch_removes_explicit_kms_packet`
- What it does: Defines test_cyclic_constructive_branch_removes_explicit_kms_packet

### `tests/test_cp1_drazin_model_residue_root_chain.py`

- Lines: `17`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_cp1_edge_residue_zero_is_derived_from_regular_nilpotent_root`
- What it does: Defines test_cp1_edge_residue_zero_is_derived_from_regular_nilpotent_root

### `tests/test_decl_graph_support.py`

- Lines: `121`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, pathlib, tempfile, tools, unittest`
- Classes: `DeclGraphSupportTests`
- What it does: Defines DeclGraphSupportTests

### `tests/test_density_weight_equilibrium_bridge_theorems.py`

- Lines: `15`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_zero_weight_density_readout_is_identified_with_comparison_readout, test_equilibrium_seed_forces_zero_weight_density_readout_packet_to_vanish`
- What it does: Defines test_zero_weight_density_readout_is_identified_with_comparison_readout, test_equilibrium_seed_forces_zero_weight_density_readout_packet_to_vanish

### `tests/test_drazin_chiral_supertrace_owner.py`

- Lines: `33`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_drazin_chiral_supertrace_owner_is_operatorial_not_dixmier, test_closure_drazin_bridge_exports_chiral_supertrace_owner_theorem`
- What it does: Defines test_drazin_chiral_supertrace_owner_is_operatorial_not_dixmier, test_closure_drazin_bridge_exports_chiral_supertrace_owner_theorem

### `tests/test_drazin_operator_corridor.py`

- Lines: `103`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `DrazinOperatorCorridorTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines DrazinOperatorCorridorTests, _run_snippet, _combined_output

### `tests/test_drazin_root_owner_chain.py`

- Lines: `33`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_singular_drazin_projector_idempotent_has_root_calculation, test_canonical_projection_idempotent_uses_singular_owner_root`
- What it does: Defines decl_block, test_singular_drazin_projector_idempotent_has_root_calculation, test_canonical_projection_idempotent_uses_singular_owner_root

### `tests/test_drazin_supergraded_translation_packet.py`

- Lines: `55`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, unittest`
- Classes: `DrazinSupergradedTranslationPacketTests`
- What it does: Defines DrazinSupergradedTranslationPacketTests

### `tests/test_enrich_tactic_path_operator_spectrum.py`

- Lines: `182`
- AST status: `ok`
- Imports: `__future__, enrich_tactic_path_operator_spectrum, json, pathlib, pytest, sys`
- Top-level functions: `_candidate, _row, test_compute_operator_spectrum_mixed_decision_point, test_enrich_row_adds_candidate_operator_weights, test_repeated_stall_family_has_cycle_pressure, test_iter_jsonl_missing_input_fails, test_run_writes_enriched_rows_and_stats, test_run_groups_rows_by_decision_point_before_enrichment`
- What it does: Defines _candidate, _row, test_compute_operator_spectrum_mixed_decision_point, test_enrich_row_adds_candidate_operator_weights, test_repeated_stall_family_has_cycle_pressure

### `tests/test_enrich_tactic_path_with_lightcone_spectrum.py`

- Lines: `63`
- AST status: `ok`
- Imports: `enrich_tactic_path_with_lightcone_spectrum, json, pathlib, sys`
- Top-level functions: `test_enrich_rows_adds_context_and_candidate_weights, test_load_spectral_report_rejects_wrong_schema, test_iter_jsonl_missing_input_fails`
- What it does: Defines test_enrich_rows_adds_context_and_candidate_weights, test_load_spectral_report_rejects_wrong_schema, test_iter_jsonl_missing_input_fails

### `tests/test_fierz_area_root_chain.py`

- Lines: `33`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_info_area_owner_root_names_cauchy_schwarz_bound, test_doubled_fierz_area_consumer_uses_owner_area_nonneg`
- What it does: Defines decl_block, test_info_area_owner_root_names_cauchy_schwarz_bound, test_doubled_fierz_area_consumer_uses_owner_area_nonneg

### `tests/test_fierz_owner_root_chain.py`

- Lines: `32`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `theorem_block, test_doubled_fierz_majorana_uses_owner_root_not_generic_wrapper, test_quantum_fierz_owner_roots_are_present`
- What it does: Defines theorem_block, test_doubled_fierz_majorana_uses_owner_root_not_generic_wrapper, test_quantum_fierz_owner_roots_are_present

### `tests/test_fierz_projection_boundary.py`

- Lines: `56`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `live_decl, test_fierz_readout_separates_projection_from_full_fierz_presentation, test_quantum_fierz_owner_roots_are_used_for_support_and_majorana_shadow, test_operatorial_fierz_derivation_is_not_named_as_spacetime_equivalence`
- What it does: Defines live_decl, test_fierz_readout_separates_projection_from_full_fierz_presentation, test_quantum_fierz_owner_roots_are_used_for_support_and_majorana_shadow, test_operatorial_fierz_derivation_is_not_named_as_spacetime_equivalence

### `tests/test_fitting_drazin_boundary.py`

- Lines: `60`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_fitting_drazin_boundary_defines_regular_and_nilpotent_parts, test_fitting_drazin_decomposition_is_algebraic_not_witness_packaging, test_fitting_drazin_complement_annihilation_roots_in_power_law_and_commutation, test_fitting_nilpotent_part_has_explicit_power_zero_boundary`
- What it does: Defines decl_block, test_fitting_drazin_boundary_defines_regular_and_nilpotent_parts, test_fitting_drazin_decomposition_is_algebraic_not_witness_packaging, test_fitting_drazin_complement_annihilation_roots_in_power_law_and_commutation, test_fitting_nilpotent_part_has_explicit_power_zero_boundary

### `tests/test_gemini_cli_guard.py`

- Lines: `93`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `run_guard, test_gemini_guard_records_then_blocks_until_interval, test_gemini_guard_check_does_not_record, test_gemini_guard_daily_cap_is_enforced, test_gemini_guard_fails_closed_on_corrupt_state`
- What it does: Defines run_guard, test_gemini_guard_records_then_blocks_until_interval, test_gemini_guard_check_does_not_record, test_gemini_guard_daily_cap_is_enforced, test_gemini_guard_fails_closed_on_corrupt_state

### `tests/test_generalized_metric_core.py`

- Lines: `127`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `GeneralizedMetricCoreTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines GeneralizedMetricCoreTests, _run_snippet, _combined_output

### `tests/test_generalized_metric_polarized_bridge.py`

- Lines: `103`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `GeneralizedMetricPolarizedBridgeTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines GeneralizedMetricPolarizedBridgeTests, _run_snippet, _combined_output

### `tests/test_generalized_metric_recomposition_bridge.py`

- Lines: `118`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `GeneralizedMetricRecompositionBridgeTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines GeneralizedMetricRecompositionBridgeTests, _run_snippet, _combined_output

### `tests/test_generate_theory_spire_viz.py`

- Lines: `34`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `networkx, tools, unittest`
- Classes: `TestGenerateTheorySpireViz`
- What it does: Defines TestGenerateTheorySpireViz

### `tests/test_generate_truth_transport.py`

- Lines: `76`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `test_generate_truth_transport_from_run_artifact`
- What it does: Defines test_generate_truth_transport_from_run_artifact

### `tests/test_gromov_witten_projective_lane_targets.py`

- Lines: `23`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_gw_and_quantum_projective_lane_targets_are_nonvacuous`
- What it does: Defines test_gw_and_quantum_projective_lane_targets_are_nonvacuous

### `tests/test_hermes_bounded_runner.py`

- Lines: `81`
- AST status: `ok`
- Imports: `pathlib, tools`
- Top-level functions: `test_extract_text_recovers_reasoning_route_block_when_content_empty, test_truth_transport_packet_carries_graph_context_and_gates`
- What it does: Defines test_extract_text_recovers_reasoning_route_block_when_content_empty, test_truth_transport_packet_carries_graph_context_and_gates

### `tests/test_hermes_leanstral_autoproof_loop.py`

- Lines: `164`
- AST status: `ok`
- Imports: `__future__, json, pathlib, tools`
- Top-level functions: `fake_lean, test_autoproof_stops_after_first_verified_candidate, test_autoproof_repairs_after_lean_error, test_autoproof_records_lean_dojo_style_repair_attempt_trace, test_autoproof_marks_strategy_switch_after_repeated_error_signature, test_autoproof_returns_failed_without_promotion_when_exhausted, test_cli_fake_candidates_prints_json`
- What it does: Defines fake_lean, test_autoproof_stops_after_first_verified_candidate, test_autoproof_repairs_after_lean_error, test_autoproof_records_lean_dojo_style_repair_attempt_trace, test_autoproof_marks_strategy_switch_after_repeated_error_signature

### `tests/test_hermes_vibe_coding_agent.py`

- Lines: `134`
- AST status: `ok`
- Imports: `__future__, json, pathlib, tools`
- Top-level functions: `test_sanitize_candidate_removes_chatml_fences_and_vibe_footer, test_build_lean_tactic_messages_are_bounded_and_local_only, test_parse_openai_chat_completion_extracts_assistant_content, test_propose_with_fake_transport_returns_proposal_packet, test_cli_prints_json_with_fake_response`
- What it does: Defines test_sanitize_candidate_removes_chatml_fences_and_vibe_footer, test_build_lean_tactic_messages_are_bounded_and_local_only, test_parse_openai_chat_completion_extracts_assistant_content, test_propose_with_fake_transport_returns_proposal_packet, test_cli_prints_json_with_fake_response

### `tests/test_hestenes_dilation_charge_mode.py`

- Lines: `21`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_dilation_charge_response_mode_packet_exists`
- What it does: Defines test_dilation_charge_response_mode_packet_exists

### `tests/test_hestenes_dirac_formalization.py`

- Lines: `155`
- AST status: `ok`
- Imports: `pathlib, subprocess`
- Top-level functions: `test_hestenes_dirac_module_declares_real_bivector_phase_not_complex_i, test_hestenes_dirac_module_declares_spinor_current_and_spin_plane_bilinears, test_hestenes_dirac_module_declares_real_dirac_equation_and_conservation_packet, test_hestenes_dirac_polar_owner_exposes_density_rotor_phase_without_complex_i, test_hestenes_dirac_polar_owner_derives_real_bilinear_readouts, test_hestenes_dirac_real_four_by_four_paffian_biquaternion_surface, test_hestenes_dirac_majorana_bdg_real_skew_pfaffian_surface, test_hestenes_dirac_concrete_realification_pfaffian_proof_layer, test_hestenes_dirac_concrete_majorana_bdg_pfaffian_proof_layer, test_hestenes_dirac_imported_by_clifford_all, test_hestenes_dirac_module_builds`
- What it does: Defines test_hestenes_dirac_module_declares_real_bivector_phase_not_complex_i, test_hestenes_dirac_module_declares_spinor_current_and_spin_plane_bilinears, test_hestenes_dirac_module_declares_real_dirac_equation_and_conservation_packet, test_hestenes_dirac_polar_owner_exposes_density_rotor_phase_without_complex_i, test_hestenes_dirac_polar_owner_derives_real_bilinear_readouts

### `tests/test_hive_arango_queue.py`

- Lines: `151`
- AST status: `ok`
- Imports: `json, pathlib, sys, tools`
- Top-level functions: `write_jsonl, test_build_goal_task_and_event_docs_from_infotree_record, test_build_fossil_doc_from_verified_logos_record, test_seed_payloads_routes_goals_and_fossils_into_queue_collections, test_schema_specs_include_queue_and_truth_collections`
- What it does: Defines write_jsonl, test_build_goal_task_and_event_docs_from_infotree_record, test_build_fossil_doc_from_verified_logos_record, test_seed_payloads_routes_goals_and_fossils_into_queue_collections, test_schema_specs_include_queue_and_truth_collections

### `tests/test_hive_autoproof_trace_schemas.py`

- Lines: `281`
- AST status: `ok`
- Imports: `__future__, copy, pathlib, tools`
- Top-level functions: `_errors, repair_attempt, autoproof_trace, seed_candidate, leanstral_task, test_repair_attempt_packet_validates_as_proposal_attempt_evidence, test_repair_attempt_packet_rejects_promotion_and_lean_checked_authority, test_repair_attempt_packet_requires_forbidden_lean_verification_use, test_autoproof_trace_packet_validates_episode_aggregate_with_attempt_refs, test_autoproof_trace_packet_rejects_missing_attempt_refs_and_promotion_allowed, test_autoproof_trace_packet_requires_forbidden_authority_gate_list, test_hermes_leanstral_policy_allows_attempt_and_trace_packets_but_not_gate_packets, test_motherbee_leanstral_task_allows_trace_sidecars, test_runner_accepts_hermes_leanstral_attempt_trace_and_candidate_outputs, test_runner_still_rejects_lean_verification_from_hermes_leanstral`
- What it does: Defines _errors, repair_attempt, autoproof_trace, seed_candidate, leanstral_task

### `tests/test_hive_bee.py`

- Lines: `492`
- AST status: `ok`
- Imports: `dataclasses, json, pathlib, sys, tools`
- Top-level functions: `sample_config, sample_goal, sample_task, sample_attempt, test_extract_tactic_supports_label_and_fenced_blocks, test_generated_theorem_source_indexes_verified_fossil, test_run_leansearch_local_retrieval_normalizes_hits, test_run_leansearch_local_retrieval_missing_records_has_actionable_error, test_run_retrieval_hybrid_merges_gravity_and_leansearch_local, test_build_deadend_doc_captures_recirculation_memory, test_build_replay_packet_contains_required_audit_fields, test_build_replay_packet_captures_declaration_indexed_fossil_context, test_fossilize_success_persists_replay_packet, test_run_one_success_fossilizes, test_run_one_failure_requeues_before_max_attempts, test_run_retrieval_dispatches_to_leansearch, test_emit_attempt_packets_marks_leansearch_source_lane, test_run_retrieval_hybrid_merges_and_dedupes`
- What it does: Defines sample_config, sample_goal, sample_task, sample_attempt, test_extract_tactic_supports_label_and_fenced_blocks

### `tests/test_hive_bee_runner.py`

- Lines: `360`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys, tools`
- Top-level functions: `source_packet, socratic_packet, execution_intent_packet, bee_task, write_json, run_cli, test_runner_appends_schema_validated_allowed_output_and_returns_bee_result, test_runner_dry_run_validates_but_writes_no_output_packet, test_runner_rejects_missing_input_packet, test_runner_rejects_invalid_output_before_append, test_runner_rejects_forbidden_output_kind, test_runner_rejects_allowed_kind_above_authority_ceiling, test_cli_writes_bee_result_and_appends_output, test_cli_dry_run_writes_no_output_packet, test_runner_rejects_role_task_kind_mismatch, test_result_contract_rejects_hash_mismatch, test_result_contract_rejects_promotion_allowed_true, test_runner_rejects_output_outside_role_policy_even_when_task_allows_it`
- What it does: Defines source_packet, socratic_packet, execution_intent_packet, bee_task, write_json

### `tests/test_hive_bee_task_result_schemas.py`

- Lines: `369`
- AST status: `ok`
- Imports: `__future__, copy, tools`
- Top-level functions: `_errors, bee_task, bee_result, _contract_errors, test_bee_task_schema_validates_ephemeral_dispatch_without_authority_field, test_bee_task_requires_promotion_decision_in_forbidden_outputs, test_bee_task_repulsion_field_accepts_packet_hashes_and_blocker_ids, test_bee_result_schema_validates_worker_return_receipt, test_autoproof_trace_packet_schema_is_proposal_only_repair_journal, test_autoproof_trace_packet_rejects_authority_inflation, test_route_invocation_packet_schema_is_navigation_only_motherbee_decision, test_route_invocation_packet_rejects_authority_inflation, test_bee_result_rejects_promotion_allowed_true, test_bee_result_rejects_malformed_packet_hash, test_task_result_contract_accepts_semantic_socrates_result, test_task_result_contract_rejects_forbidden_authority_output, test_task_result_contract_rejects_allowed_but_too_high_authority_kind, test_invalid_assigned_role_fails_closed`
- What it does: Defines _errors, bee_task, bee_result, _contract_errors, test_bee_task_schema_validates_ephemeral_dispatch_without_authority_field

### `tests/test_hive_cognitive_packet_schemas.py`

- Lines: `145`
- AST status: `ok`
- Imports: `__future__, copy, tools`
- Top-level functions: `_errors, test_source_observation_packet_validates_navigation_sensation, test_symbolic_motif_packet_rejects_promotion_authority, test_socratic_question_packet_requires_question_not_proof`
- What it does: Defines _errors, test_source_observation_packet_validates_navigation_sensation, test_symbolic_motif_packet_rejects_promotion_authority, test_socratic_question_packet_requires_question_not_proof

### `tests/test_hive_json_ingestor.py`

- Lines: `110`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `test_ingest_hive_json_normalizes_and_hashes_packets, test_ingest_hive_json_from_real_lean_output`
- What it does: Defines test_ingest_hive_json_normalizes_and_hashes_packets, test_ingest_hive_json_from_real_lean_output

### `tests/test_hive_leanstral_bee_worker.py`

- Lines: `304`
- AST status: `ok`
- Imports: `__future__, json, pathlib, pytest, tools`
- Top-level functions: `base_task, seed_packet, fake_verified, fake_failed, test_worker_emits_probe_ready_candidate_and_bee_result, test_worker_emits_residue_after_exhausting_retries, test_worker_rejects_each_authority_gate_output_in_task_contract, test_worker_rejects_authority_ceiling_above_proposal, test_worker_success_never_claims_lean_checked_authority, test_worker_dry_run_appends_nothing, test_worker_requires_all_authority_gate_kinds_to_be_forbidden`
- What it does: Defines base_task, seed_packet, fake_verified, fake_failed, test_worker_emits_probe_ready_candidate_and_bee_result

### `tests/test_hive_local_packet_store.py`

- Lines: `162`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys, tools`
- Top-level functions: `source_packet, write_packet, run_cli, test_append_valid_packet_computes_hash_and_survives_reload, test_append_rejects_invalid_packet, test_duplicate_hash_is_idempotently_ignored, test_duplicate_id_with_different_hash_rejected, test_cli_list_filters_by_kind_authority_and_lineage, test_show_parents_children_and_lineage`
- What it does: Defines source_packet, write_packet, run_cli, test_append_valid_packet_computes_hash_and_survives_reload, test_append_rejects_invalid_packet

### `tests/test_hive_logos_semantics.py`

- Lines: `26`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_hive_logos_defines_distinct_partial_and_strict_paths, test_hive_logos_indexes_declaration_conclusions_via_forall_telescope`
- What it does: Defines test_hive_logos_defines_distinct_partial_and_strict_paths, test_hive_logos_indexes_declaration_conclusions_via_forall_telescope

### `tests/test_hive_logos_tracer.py`

- Lines: `18`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_hive_logos_module_exposes_tracer_bullet_commands`
- What it does: Defines test_hive_logos_module_exposes_tracer_bullet_commands

### `tests/test_hive_motherbee.py`

- Lines: `572`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys, tools`
- Top-level functions: `source_packet, theorem_candidate, pauli_packet, socratic_packet, leanstral_residue, repair_attempt, autoproof_trace, run_cli, test_discover_tasks_routes_captured_source_observation_to_socratesbee, test_once_appends_beetask_as_append_only_routing_receipt, test_once_is_idempotent_after_beetask_exists, test_dry_run_prints_tasks_without_mutating_store, test_limit_and_priority_are_deterministic, test_non_matching_status_is_not_scheduled, test_cli_once_appends_task, test_cli_dry_run_does_not_append_task, test_hermes_leanstral_requires_new_pauli_or_socratic_information, test_hermes_leanstral_task_is_scheduled_after_pauli_critique`
- What it does: Defines source_packet, theorem_candidate, pauli_packet, socratic_packet, leanstral_residue

### `tests/test_hive_multichecker_merge.py`

- Lines: `97`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `write_jsonl, test_merge_reports_combines_checker_rows, test_cli_writes_json_and_markdown`
- What it does: Defines write_jsonl, test_merge_reports_combines_checker_rows, test_cli_writes_json_and_markdown

### `tests/test_hive_spec_submission_policy.py`

- Lines: `201`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_target_spec_and_submission_packets_match_expected_declarations, test_submission_with_unsound_marker_blocks_pair, test_promotion_gate_requires_build_paranoia_and_safeverify, test_promotion_gate_rejects_failed_safeverify, test_promotion_gate_records_autograder_points_and_rejects_failure, test_cli_builds_packets_and_gate`
- What it does: Defines test_target_spec_and_submission_packets_match_expected_declarations, test_submission_with_unsound_marker_blocks_pair, test_promotion_gate_requires_build_paranoia_and_safeverify, test_promotion_gate_rejects_failed_safeverify, test_promotion_gate_records_autograder_points_and_rejects_failure

### `tests/test_hive_swarm.py`

- Lines: `131`
- AST status: `ok`
- Imports: `pathlib, sys, tools`
- Top-level functions: `sample_swarm_config, sample_goal, sample_task, test_parse_critic_decision_and_auditor_report, test_run_one_success_with_all_roles, test_run_one_critic_rejection_requeues`
- What it does: Defines sample_swarm_config, sample_goal, sample_task, test_parse_critic_decision_and_auditor_report, test_run_one_success_with_all_roles

### `tests/test_hive_translation_control_packet.py`

- Lines: `89`
- AST status: `ok`
- Imports: `__future__, copy, tools`
- Top-level functions: `_errors, test_translation_control_packet_validates_type_directed_controls, test_translation_control_packet_rejects_proof_authority_and_missing_proof_ban, test_translation_control_packet_requires_symbol_controls`
- What it does: Defines _errors, test_translation_control_packet_validates_type_directed_controls, test_translation_control_packet_rejects_proof_authority_and_missing_proof_ban, test_translation_control_packet_requires_symbol_controls

### `tests/test_hive_workflow_policy.py`

- Lines: `116`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_declaration_header_ignores_body_changes, test_prove_mode_rejects_header_change, test_formalize_mode_allows_header_change, test_review_mode_is_read_only, test_checkpoint_requires_build_and_axiom_gates, test_unsound_markers_are_rejected_by_default, test_cli_writes_report_and_returns_nonzero_on_violation`
- What it does: Defines test_declaration_header_ignores_body_changes, test_prove_mode_rejects_header_change, test_formalize_mode_allows_header_change, test_review_mode_is_read_only, test_checkpoint_requires_build_and_axiom_gates

### `tests/test_hydrate_arango_topology.py`

- Lines: `77`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_hydrate_preserves_raw_edges_and_adds_layered_scc_overlay`
- What it does: Defines test_hydrate_preserves_raw_edges_and_adds_layered_scc_overlay

### `tests/test_hydrated_dag_to_lean_graph.py`

- Lines: `196`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys`
- Top-level functions: `_write_fixture, _component, _run_adapter, test_hydrated_dag_to_lean_graph_apex_slice_has_closed_references_and_meta, test_hydrated_dag_to_lean_graph_fails_fast_on_duplicate_representatives, test_hydrated_dag_to_lean_graph_fails_fast_on_self_dependency`
- What it does: Defines _write_fixture, _component, _run_adapter, test_hydrated_dag_to_lean_graph_apex_slice_has_closed_references_and_meta, test_hydrated_dag_to_lean_graph_fails_fast_on_duplicate_representatives

### `tests/test_improver_external_stack.py`

- Lines: `67`
- AST status: `ok`
- Imports: `__future__, os, pathlib, sys`
- Top-level functions: `test_improver_external_stack_imports_offline_metrics, test_improver_prompt_routes_leanstral_to_local_openai_endpoint`
- What it does: Defines test_improver_external_stack_imports_offline_metrics, test_improver_prompt_routes_leanstral_to_local_openai_endpoint

### `tests/test_improver_trace_bridge.py`

- Lines: `84`
- AST status: `ok`
- Imports: `__future__, csv, improver_trace_bridge, json, pathlib, pytest, sys`
- Top-level functions: `test_normalize_improved_length_rewrite_candidate, test_normalize_failed_rewrite_is_failure_telemetry, test_run_reads_csv_and_writes_stats, test_iter_records_missing_input_fails`
- What it does: Defines test_normalize_improved_length_rewrite_candidate, test_normalize_failed_rewrite_is_failure_telemetry, test_run_reads_csv_and_writes_stats, test_iter_records_missing_input_fails

### `tests/test_incompressible_bit_bridge.py`

- Lines: `40`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_incompressible_bit_bridge_exposes_relative_volume_and_cramer_rao_bits, test_anomaly_scale_uses_negative_cramer_rao_log_volume_redline, test_incompressible_bit_bridge_is_wired_into_canonical_umbrella`
- What it does: Defines test_incompressible_bit_bridge_exposes_relative_volume_and_cramer_rao_bits, test_anomaly_scale_uses_negative_cramer_rao_log_volume_redline, test_incompressible_bit_bridge_is_wired_into_canonical_umbrella

### `tests/test_incompressible_cramer_rao_action_bridge.py`

- Lines: `63`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_incompressible_cramer_rao_action_bridge_surface, test_incompressible_bit_bridge_surface, test_incompressible_cramer_rao_action_bridge_operatorial_redline, test_incompressible_cramer_rao_action_bridge_imported_by_all`
- What it does: Defines test_incompressible_cramer_rao_action_bridge_surface, test_incompressible_bit_bridge_surface, test_incompressible_cramer_rao_action_bridge_operatorial_redline, test_incompressible_cramer_rao_action_bridge_imported_by_all

### `tests/test_infinite_owner_hessian_context.py`

- Lines: `82`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `read_source, test_smooth_legendre_gram_owner_replaces_explicit_fisher_positivity_packets, test_smooth_legendre_gram_readout_derives_fisher_laws_and_packet, test_log_partition_fisher_covariance_owner_replaces_log_and_covariance_packets, test_log_partition_fisher_covariance_owner_derives_context_packet, test_hessian_module_builds_with_smooth_legendre_gram_owner`
- What it does: Defines read_source, test_smooth_legendre_gram_owner_replaces_explicit_fisher_positivity_packets, test_smooth_legendre_gram_readout_derives_fisher_laws_and_packet, test_log_partition_fisher_covariance_owner_replaces_log_and_covariance_packets, test_log_partition_fisher_covariance_owner_derives_context_packet

### `tests/test_infinite_owner_kms_context.py`

- Lines: `90`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `read_source, block_between, test_cyclic_modular_time_context_replaces_explicit_kms_packet, test_cyclic_modular_time_context_derives_kms_and_modular_time, test_observable_cyclic_fisher_context_replaces_metric_gauge_sld_packets, test_observable_cyclic_fisher_context_derives_metric_gauge_and_packet, test_module_builds_with_infinite_owner_kms_context`
- What it does: Defines read_source, block_between, test_cyclic_modular_time_context_replaces_explicit_kms_packet, test_cyclic_modular_time_context_derives_kms_and_modular_time, test_observable_cyclic_fisher_context_replaces_metric_gauge_sld_packets

### `tests/test_ingest_semantic_content_audit.py`

- Lines: `137`
- AST status: `ok`
- Imports: `tools`
- Top-level functions: `test_graph_context_uses_local_reverse_dependency_edges, test_graph_context_prefers_enclosing_declaration_when_known, test_priority_combines_severity_importers_and_reverse_impact, test_build_rows_creates_findings_and_repair_tasks, test_min_status_filters_less_severe_hive_tasks, test_finding_and_task_keys_are_idempotent_across_runs`
- What it does: Defines test_graph_context_uses_local_reverse_dependency_edges, test_graph_context_prefers_enclosing_declaration_when_known, test_priority_combines_severity_importers_and_reverse_impact, test_build_rows_creates_findings_and_repair_tasks, test_min_status_filters_less_severe_hive_tasks

### `tests/test_injection_common_gpu_snapshot.py`

- Lines: `24`
- AST status: `ok`
- Imports: `importlib, sys, types`
- Top-level functions: `test_current_gpu_memory_snapshot_handles_na_values`
- What it does: Defines test_current_gpu_memory_snapshot_handles_na_values

### `tests/test_jixia_batch_training.py`

- Lines: `214`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_write_raw_jixia_fixture, test_discover_lean_files_is_deduped_and_sorted_by_prefix, test_lean_files_from_cone_packet_collects_source_excerpts, test_concat_jsonl_skips_missing_inputs, test_run_pipeline_skip_jixia_builds_training_from_existing_raw, test_run_pipeline_skip_jixia_accepts_cone_packet, test_jixia_batch_training_cli_skip_jixia`
- What it does: Defines _write_raw_jixia_fixture, test_discover_lean_files_is_deduped_and_sorted_by_prefix, test_lean_files_from_cone_packet_collects_source_excerpts, test_concat_jsonl_skips_missing_inputs, test_run_pipeline_skip_jixia_builds_training_from_existing_raw

### `tests/test_jixia_trace_bridge.py`

- Lines: `176`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_normalize_symbol_converts_name_arrays_and_references, test_run_bridge_writes_all_sidecars, test_run_bridge_classifies_aggregate_tactic_container, test_jixia_trace_bridge_cli`
- What it does: Defines test_normalize_symbol_converts_name_arrays_and_references, test_run_bridge_writes_all_sidecars, test_run_bridge_classifies_aggregate_tactic_container, test_jixia_trace_bridge_cli

### `tests/test_kanban_evidence_lint.py`

- Lines: `84`
- AST status: `ok`
- Imports: `json, pathlib, subprocess`
- Top-level functions: `run_lint, test_jsonl_starting_with_object_rows_is_parsed, test_gate_fails_on_missing_advanced_state_evidence, test_gate_passes_with_build_and_audit_evidence`
- What it does: Defines run_lint, test_jsonl_starting_with_object_rows_is_parsed, test_gate_fails_on_missing_advanced_state_evidence, test_gate_passes_with_build_and_audit_evidence

### `tests/test_kkt_corridor.py`

- Lines: `164`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `KKTCorridorTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines KKTCorridorTests, _run_snippet, _combined_output

### `tests/test_kkt_exact_residual_packet.py`

- Lines: `12`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_exact_residuals_construct_kkt_shadow`
- What it does: Defines test_exact_residuals_construct_kkt_shadow

### `tests/test_kkt_stationarity_exact_branch.py`

- Lines: `12`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_kkt_stationarity_exact_branch_exists`
- What it does: Defines test_kkt_stationarity_exact_branch_exists

### `tests/test_lean_auto_trace_bridge.py`

- Lines: `83`
- AST status: `ok`
- Imports: `__future__, json, lean_auto_trace_bridge, pathlib, pytest, sys`
- Top-level functions: `test_normalize_trusted_smt_trace_is_not_authority, test_normalize_reconstructed_native_trace_can_be_training_positive, test_run_reads_jsonl_and_writes_stats, test_iter_records_missing_input_fails`
- What it does: Defines test_normalize_trusted_smt_trace_is_not_authority, test_normalize_reconstructed_native_trace_can_be_training_positive, test_run_reads_jsonl_and_writes_stats, test_iter_records_missing_input_fails

### `tests/test_lean_autograder_report_bridge.py`

- Lines: `65`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_normalize_autograder_payload_scores_problem_rows, test_cli_normalizes_existing_autograder_json`
- What it does: Defines test_normalize_autograder_payload_scores_problem_rows, test_cli_normalizes_existing_autograder_json

### `tests/test_lean_improver_probe.py`

- Lines: `54`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys`
- Top-level functions: `test_lean_improver_probe_ranks_non_mutating_candidates`
- What it does: Defines test_lean_improver_probe_ranks_non_mutating_candidates

### `tests/test_lean_interact_wrapper.py`

- Lines: `25`
- AST status: `ok`
- Imports: `tools`
- Top-level functions: `test_get_proof_state_reports_goal, test_apply_tactic_accepts_valid_tactic, test_apply_tactic_rejects_invalid_tactic`
- What it does: Defines test_get_proof_state_reports_goal, test_apply_tactic_accepts_valid_tactic, test_apply_tactic_rejects_invalid_tactic

### `tests/test_leandojo_v2_bridge.py`

- Lines: `178`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `write_json_payload, write_jsonl_payload, test_convert_theorem_record_to_bridge_row, test_convert_theorem_record_accepts_schema_aliases, test_run_bridge_converts_json_to_jsonl, test_run_bridge_converts_jsonl_and_writes_coverage_report, test_load_decl_names_accepts_decl_name_lists_and_hydrated_components`
- What it does: Defines write_json_payload, write_jsonl_payload, test_convert_theorem_record_to_bridge_row, test_convert_theorem_record_accepts_schema_aliases, test_run_bridge_converts_json_to_jsonl

### `tests/test_leanparanoia_audit_bridge.py`

- Lines: `65`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_normalize_paranoia_payload_flattens_failures, test_cli_normalizes_existing_json_report`
- What it does: Defines test_normalize_paranoia_payload_flattens_failures, test_cli_normalizes_existing_json_report

### `tests/test_leansearch_local.py`

- Lines: `72`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `_write_jsonl, test_tokenize_keeps_lean_identifier_words, test_build_records_and_search_rank_local_declarations`
- What it does: Defines _write_jsonl, test_tokenize_keeps_lean_identifier_words, test_build_records_and_search_rank_local_declarations

### `tests/test_lightcone_spectral_filter.py`

- Lines: `80`
- AST status: `ok`
- Imports: `json, lightcone_spectral_filter, numpy, pathlib, pytest, sys`
- Top-level functions: `test_compute_drazin_from_schur_keeps_off_diagonal_correction, test_build_report_from_lean_graph_slice, test_build_report_refuses_unbounded_dense_slice, test_recurrent_two_node_cycle_has_nonzero_spectral_core, test_pure_dag_chain_has_trivial_drazin_core`
- What it does: Defines test_compute_drazin_from_schur_keeps_off_diagonal_correction, test_build_report_from_lean_graph_slice, test_build_report_refuses_unbounded_dense_slice, test_recurrent_two_node_cycle_has_nonzero_spectral_core, test_pure_dag_chain_has_trivial_drazin_core

### `tests/test_logipedia_markdown_distill.py`

- Lines: `180`
- AST status: `ok`
- Imports: `__future__, copy, json, pathlib, subprocess, sys, tools`
- Top-level functions: `_errors, test_classify_claim_separates_owner_projection_constructive_gap_and_analytic_gate, test_distill_markdown_extracts_ranked_entries_and_lean_blocks, test_theorem_bank_entry_packet_schema_accepts_ranked_non_authority_entry, test_owner_audit_packet_schema_requires_non_promoting_owner_decision, test_cli_writes_entries_owner_audits_and_ranked_queue`
- What it does: Defines _errors, test_classify_claim_separates_owner_projection_constructive_gap_and_analytic_gate, test_distill_markdown_extracts_ranked_entries_and_lean_blocks, test_theorem_bank_entry_packet_schema_accepts_ranked_non_authority_entry, test_owner_audit_packet_schema_requires_non_promoting_owner_decision

### `tests/test_logsumexp_hol_derivative_root_chain.py`

- Lines: `41`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_logsumexp_derivative_root_is_hasderivat_chain, test_softmax_consumes_logsumexp_derivative_export_not_chain_root`
- What it does: Defines decl_block, test_logsumexp_derivative_root_is_hasderivat_chain, test_softmax_consumes_logsumexp_derivative_export_not_chain_root

### `tests/test_majorana_equilibrium_seed_bridge.py`

- Lines: `21`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_majorana_k_split_uses_equilibrium_seed_theorem`
- What it does: Defines test_majorana_k_split_uses_equilibrium_seed_theorem

### `tests/test_mathfulness_audit.py`

- Lines: `138`
- AST status: `ok`
- Imports: `__future__, json, pathlib, subprocess, sys`
- Top-level functions: `_write_required_inputs, _run_audit, _write_decl, _single_classification, test_true_only_trivial_theorem_is_vacuous_or_surrogate, test_named_bridge_context_is_review_hint_not_promotion, test_gate_fails_empty_selected_prefix_and_reports_global_failure, test_gate_fails_when_required_inputs_missing, test_missing_source_block_is_audit_missing_and_gate_failure`
- What it does: Defines _write_required_inputs, _run_audit, _write_decl, _single_classification, test_true_only_trivial_theorem_is_vacuous_or_surrogate

### `tests/test_metric_transport_witness.py`

- Lines: `80`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `MetricTransportWitnessTests`
- Top-level functions: `has_decl`
- What it does: Defines MetricTransportWitnessTests, has_decl

### `tests/test_millennium_problem_bridge.py`

- Lines: `86`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_fixture_repo, test_extract_status_table_reads_readme_rows, test_build_records_marks_external_context_only, test_millennium_problem_bridge_cli_writes_records`
- What it does: Defines _fixture_repo, test_extract_status_table_reads_readme_rows, test_build_records_marks_external_context_only, test_millennium_problem_bridge_cli_writes_records

### `tests/test_moore_penrose_projector_own_range_adapter.py`

- Lines: `71`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_canonical_mp_projectors_have_generic_own_range_starprojection_readbacks, test_canonical_mp_projectors_expose_range_and_kernel_orthogonal_readbacks, test_cik_own_range_readbacks_can_be_seen_as_consumers_of_generic_mp_adapters`
- What it does: Defines decl_block, test_canonical_mp_projectors_have_generic_own_range_starprojection_readbacks, test_canonical_mp_projectors_expose_range_and_kernel_orthogonal_readbacks, test_cik_own_range_readbacks_can_be_seen_as_consumers_of_generic_mp_adapters

### `tests/test_moore_penrose_root_projector_chain.py`

- Lines: `39`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_moore_penrose_owner_has_beginning_projector_root_lemmas, test_certified_inverse_kernel_consumes_moore_penrose_projector_exports`
- What it does: Defines decl_block, test_moore_penrose_owner_has_beginning_projector_root_lemmas, test_certified_inverse_kernel_consumes_moore_penrose_projector_exports

### `tests/test_neutral_phase_space_corridor.py`

- Lines: `100`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `NeutralPhaseSpaceCorridorSmokeTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines NeutralPhaseSpaceCorridorSmokeTests, _run_snippet, _combined_output

### `tests/test_observer_defect_strain_zero_bridge.py`

- Lines: `15`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_zero_strain_constructs_observer_defect_zd_control`
- What it does: Defines test_zero_strain_constructs_observer_defect_zd_control

### `tests/test_onsager_equilibrium_seed_bridge.py`

- Lines: `19`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_onsager_stationary_uses_equilibrium_seed_theorem`
- What it does: Defines test_onsager_stationary_uses_equilibrium_seed_theorem

### `tests/test_open_problem_formalization.py`

- Lines: `224`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `OpenProblemFormalizationTests`
- Top-level functions: `has_decl`
- What it does: Defines OpenProblemFormalizationTests, has_decl

### `tests/test_operator_owner_map_v2.py`

- Lines: `117`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `OperatorOwnerMapV2Tests`
- Top-level functions: `has_decl`
- What it does: Defines OperatorOwnerMapV2Tests, has_decl

### `tests/test_operatorial_dilation_goldstone_charge_packet.py`

- Lines: `16`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_operatorial_dilation_goldstone_charge_packet_surface`
- What it does: Defines test_operatorial_dilation_goldstone_charge_packet_surface

### `tests/test_operatorial_partition_supervolume_bridge_owner_theorem.py`

- Lines: `21`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_operatorial_partition_should_have_exact_supervolume_bridge_theorem`
- What it does: Defines test_operatorial_partition_should_have_exact_supervolume_bridge_theorem

### `tests/test_operatorial_souriau_fisher_metric_packet.py`

- Lines: `16`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_operatorial_souriau_fisher_metric_packet_surface`
- What it does: Defines test_operatorial_souriau_fisher_metric_packet_surface

### `tests/test_operatorial_weyl_supercharacter_bridge.py`

- Lines: `22`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_operatorial_weyl_character_and_supercharacter_are_source_owned`
- What it does: Defines test_operatorial_weyl_character_and_supercharacter_are_source_owned

### `tests/test_paperproof_bidirectional_cone.py`

- Lines: `107`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_build_bidirectional_cone_glues_forward_forest_to_backward_cone, test_paperproof_bidirectional_cone_cli`
- What it does: Defines test_build_bidirectional_cone_glues_forward_forest_to_backward_cone, test_paperproof_bidirectional_cone_cli

### `tests/test_paperproof_jixia_compare.py`

- Lines: `81`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_build_report_matches_paperproof_trace_against_jixia, test_render_markdown_contains_group_summary`
- What it does: Defines test_build_report_matches_paperproof_trace_against_jixia, test_render_markdown_contains_group_summary

### `tests/test_paperproof_proof_forest.py`

- Lines: `82`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_build_forest_creates_goal_tactic_and_hypothesis_edges, test_paperproof_proof_forest_cli`
- What it does: Defines test_build_forest_creates_goal_tactic_and_hypothesis_edges, test_paperproof_proof_forest_cli

### `tests/test_paperproof_rpc_export_schema.py`

- Lines: `55`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_packet_from_paperproof_rpc_array, test_packet_from_wrapped_webview_shape`
- What it does: Defines test_packet_from_paperproof_rpc_array, test_packet_from_wrapped_webview_shape

### `tests/test_paperproof_tableau_detector.py`

- Lines: `66`
- AST status: `ok`
- Imports: `json, tools`
- Top-level functions: `test_profile_trace_detects_tableau_like_contradiction_shape, test_training_effects_adds_tableau_labels`
- What it does: Defines test_profile_trace_detects_tableau_like_contradiction_shape, test_training_effects_adds_tableau_labels

### `tests/test_paperproof_trace_bridge.py`

- Lines: `89`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_build_packets_from_jixia_tactics, test_build_packets_preserves_aggregate_tactic_classification, test_render_markdown_mentions_goals_and_tactics`
- What it does: Defines test_build_packets_from_jixia_tactics, test_build_packets_preserves_aggregate_tactic_classification, test_render_markdown_mentions_goals_and_tactics

### `tests/test_pda_forml4_bridge.py`

- Lines: `79`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_normalize_forml4_record_with_process_label, test_run_bridge_writes_jsonl_and_summary, test_pda_forml4_bridge_cli`
- What it does: Defines test_normalize_forml4_record_with_process_label, test_run_bridge_writes_jsonl_and_summary, test_pda_forml4_bridge_cli

### `tests/test_phase_a_full_suite.py`

- Lines: `246`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, tools`
- Top-level functions: `test_pos_valid_and_invalid_shapes, test_convert_theorem_record_handles_missing_tactics, test_convert_theorem_record_normalizes_tactics, test_run_bridge_multiple_files_and_rows, test_run_bridge_ignores_non_json_files, test_bridge_cli_end_to_end, test_l0_architecture_contract_surface, test_l0_modules_compile_gate`
- What it does: Defines test_pos_valid_and_invalid_shapes, test_convert_theorem_record_handles_missing_tactics, test_convert_theorem_record_normalizes_tactics, test_run_bridge_multiple_files_and_rows, test_run_bridge_ignores_non_json_files

### `tests/test_phase_a_leandojo_l0.py`

- Lines: `58`
- AST status: `ok`
- Imports: `json, pathlib, tools`
- Top-level functions: `test_phase_a_bridge_accepts_leandojo_v2_style_json, test_l0_level_contract_files_exist_and_labels_present`
- What it does: Defines test_phase_a_bridge_accepts_leandojo_v2_style_json, test_l0_level_contract_files_exist_and_labels_present

### `tests/test_phase_space_causal_flow_bridge.py`

- Lines: `158`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `PhaseSpaceCausalFlowBridgeTests`
- Top-level functions: `_run_snippet, _ensure_built, _combined_output`
- What it does: Defines PhaseSpaceCausalFlowBridgeTests, _run_snippet, _ensure_built, _combined_output

### `tests/test_phase_space_conformal_kkt_bridge.py`

- Lines: `146`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `PhaseSpaceConformalKKTBridgeTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines PhaseSpaceConformalKKTBridgeTests, _run_snippet, _combined_output

### `tests/test_phase_space_generalized_metric.py`

- Lines: `141`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `PhaseSpaceGeneralizedMetricTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines PhaseSpaceGeneralizedMetricTests, _run_snippet, _combined_output

### `tests/test_phase_space_recomposition_bridge.py`

- Lines: `333`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `PhaseSpaceRecompositionBridgeTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines PhaseSpaceRecompositionBridgeTests, _run_snippet, _combined_output

### `tests/test_phase_space_recomposition_example.py`

- Lines: `133`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `PhaseSpaceRecompositionExampleTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines PhaseSpaceRecompositionExampleTests, _run_snippet, _combined_output

### `tests/test_phase_space_weyl_causal_bridge.py`

- Lines: `302`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `PhaseSpaceWeylCausalBridgeTests`
- Top-level functions: `_run_snippet, _ensure_built, _combined_output`
- What it does: Defines PhaseSpaceWeylCausalBridgeTests, _run_snippet, _ensure_built, _combined_output

### `tests/test_ported_operator_bridges.py`

- Lines: `48`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_operators_bridge_surface, test_operator_thermo_bridge_surface, test_operatorial_fierz_bridge_surface, test_ported_operator_bridges_imported_by_all`
- What it does: Defines test_operators_bridge_surface, test_operator_thermo_bridge_surface, test_operatorial_fierz_bridge_surface, test_ported_operator_bridges_imported_by_all

### `tests/test_positive_adjoint_square_boundary.py`

- Lines: `62`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `decl_block, test_positive_adjoint_square_imports_mathlib_positive_operator_api, test_adjoint_comp_self_positive_routes_to_mathlib_root, test_endomorphism_star_squares_are_positive_and_not_witness_packaged`
- What it does: Defines decl_block, test_positive_adjoint_square_imports_mathlib_positive_operator_api, test_adjoint_comp_self_positive_routes_to_mathlib_root, test_endomorphism_star_squares_are_positive_and_not_witness_packaged

### `tests/test_predigestion_packets.py`

- Lines: `111`
- AST status: `ok`
- Imports: `json, pathlib, pytest, subprocess, sys, tools`
- Top-level functions: `write_jsonl, test_predigestion_packet_has_deterministic_id_and_boundary, test_invalid_enum_fails, test_hive_task_materializes_non_authoritative_queue_packet, test_cli_builds_claims_and_tasks`
- What it does: Defines write_jsonl, test_predigestion_packet_has_deterministic_id_and_boundary, test_invalid_enum_fails, test_hive_task_materializes_non_authoritative_queue_packet, test_cli_builds_claims_and_tasks

### `tests/test_projector_anomaly_transport_sync_v2.py`

- Lines: `83`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, re, unittest`
- Classes: `ProjectorAnomalyTransportSyncV2Tests`
- Top-level functions: `has_decl`
- What it does: Defines ProjectorAnomalyTransportSyncV2Tests, has_decl

### `tests/test_projector_noncommutativity_dilation_closure.py`

- Lines: `84`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `ProjectorNoncommutativityDilationClosureTests`
- Top-level functions: `has_decl`
- What it does: Defines ProjectorNoncommutativityDilationClosureTests, has_decl

### `tests/test_python_script_smoke.py`

- Lines: `80`
- AST status: `ok`
- Imports: `__future__, ast, pathlib, py_compile, subprocess`
- Top-level functions: `repository_python_files, test_repository_python_files_compile, test_legacy_tools_are_import_safe_and_main_guarded`
- What it does: Defines repository_python_files, test_repository_python_files_compile, test_legacy_tools_are_import_safe_and_main_guarded

### `tests/test_real_prover_trace_bridge.py`

- Lines: `89`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_real_payload, test_normalize_real_record_preserves_search_nodes, test_run_bridge_writes_jsonl_and_summary, test_real_prover_trace_bridge_cli`
- What it does: Defines _real_payload, test_normalize_real_record_preserves_search_nodes, test_run_bridge_writes_jsonl_and_summary, test_real_prover_trace_bridge_cli

### `tests/test_refresh_blueprint_tags.py`

- Lines: `44`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `tools, unittest`
- Classes: `RefreshBlueprintTagsTests`
- What it does: Defines RefreshBlueprintTagsTests

### `tests/test_relative_modular_recomposition.py`

- Lines: `131`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `RelativeModularRecompositionTests`
- Top-level functions: `_run_snippet, _combined_output`
- What it does: Defines RelativeModularRecompositionTests, _run_snippet, _combined_output

### `tests/test_representation_depth_export.py`

- Lines: `255`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, pathlib, tempfile, tools, unittest`
- Classes: `RepresentationDepthExportTests`
- Top-level functions: `_render_name, _write_jsonl, _node, _edge, _load_export, _rows_by_name, _find_row`
- What it does: Defines RepresentationDepthExportTests, _render_name, _write_jsonl, _node, _edge, _load_export

### `tests/test_rethlas_verification_bridge.py`

- Lines: `94`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `_wrong_payload, test_validate_rethlas_payload_enforces_verdict_contract, test_normalize_rethlas_payload_marks_audit_not_proof, test_rethlas_verification_bridge_cli_writes_summary, test_run_bridge_counts_invalid_contracts`
- What it does: Defines _wrong_payload, test_validate_rethlas_payload_enforces_verdict_contract, test_normalize_rethlas_payload_marks_audit_not_proof, test_rethlas_verification_bridge_cli_writes_summary, test_run_bridge_counts_invalid_contracts

### `tests/test_run_copilot_codex_lean_pipeline.py`

- Lines: `43`
- AST status: `ok`
- Imports: `pathlib, tools`
- Top-level functions: `test_build_codex_prompt_mentions_copilot_and_lean_verification_paths, test_build_pipeline_payload_records_stage_artifacts`
- What it does: Defines test_build_codex_prompt_mentions_copilot_and_lean_verification_paths, test_build_pipeline_payload_records_stage_artifacts

### `tests/test_run_gemini_guarded.py`

- Lines: `67`
- AST status: `ok`
- Imports: `json, os, pathlib, subprocess`
- Top-level functions: `test_guarded_wrapper_check_does_not_record, test_guarded_wrapper_runs_fake_gemini_and_records, test_guarded_wrapper_refuses_non_gemini_command`
- What it does: Defines test_guarded_wrapper_check_does_not_record, test_guarded_wrapper_runs_fake_gemini_and_records, test_guarded_wrapper_refuses_non_gemini_command

### `tests/test_run_predigestion_to_hive_demo.py`

- Lines: `73`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `write_jsonl, test_run_demo_writes_claims_tasks_and_summary, test_cli_run_demo`
- What it does: Defines write_jsonl, test_run_demo_writes_claims_tasks_and_summary, test_cli_run_demo

### `tests/test_run_proof_prompt_batch.py`

- Lines: `109`
- AST status: `ok`
- Imports: `pathlib, tools`
- Top-level functions: `test_extract_completion_text_prefers_message_content, test_extract_completion_text_falls_back_to_reasoning_content, test_backend_defaults_for_openai, test_backend_defaults_for_copilot, test_assess_output_quality_accepts_structured_proof_reconstruction, test_assess_output_quality_flags_repetitive_low_value_output, test_build_result_payload_records_prompt_and_output`
- What it does: Defines test_extract_completion_text_prefers_message_content, test_extract_completion_text_falls_back_to_reasoning_content, test_backend_defaults_for_openai, test_backend_defaults_for_copilot, test_assess_output_quality_accepts_structured_proof_reconstruction

### `tests/test_safeverify_audit_bridge.py`

- Lines: `83`
- AST status: `ok`
- Imports: `json, pathlib, subprocess, sys, tools`
- Top-level functions: `test_normalize_safeverify_success_outcome, test_normalize_safeverify_failure_outcome, test_cli_normalizes_existing_json_report`
- What it does: Defines test_normalize_safeverify_success_outcome, test_normalize_safeverify_failure_outcome, test_cli_normalizes_existing_json_report

### `tests/test_selfdual_chiral_partition_witness.py`

- Lines: `21`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_selfdual_chiral_lightcone_partition_witness_surface`
- What it does: Defines test_selfdual_chiral_lightcone_partition_witness_surface

### `tests/test_semantic_content_audit.py`

- Lines: `161`
- AST status: `ok`
- Imports: `pathlib, tools`
- Top-level functions: `test_proof_hole_blocks_before_other_categories, test_axiom_is_assumption_bearing_blocker, test_trivial_true_surface_is_vacuous_review_not_canonical, test_clean_surface_is_only_clean_by_this_audit, test_quarantine_manifest_has_own_status, test_commented_import_is_not_counted_as_importer, test_importer_classes_separate_unstable_umbrella_and_canonical, test_forbidden_importers_apply_to_nonpromotable_statuses, test_manifested_clean_quarantine_still_has_forbidden_importers, test_manifest_only_rows_preserve_forbidden_importer_metadata, test_in_scope_applies_file_prefixes_to_manifest_rows, test_gate_empty_selection_is_reported_by_selected_file_count, test_enclosing_decl_finds_nearest_preceding_declaration`
- What it does: Defines test_proof_hole_blocks_before_other_categories, test_axiom_is_assumption_bearing_blocker, test_trivial_true_surface_is_vacuous_review_not_canonical, test_clean_surface_is_only_clean_by_this_audit, test_quarantine_manifest_has_own_status

### `tests/test_sinkhorn_clock_defect_constructive_bound.py`

- Lines: `53`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_detailed_equilibrium_uses_theorem_backed_clock_defect_bound, test_router_equilibrium_chain_reaches_mathlib_norm_and_clock_defect_roots, test_zero_residual_readback_reaches_owner_detailed_equilibrium, test_zero_residual_constructs_real_monotone_sinkhorn_step`
- What it does: Defines test_detailed_equilibrium_uses_theorem_backed_clock_defect_bound, test_router_equilibrium_chain_reaches_mathlib_norm_and_clock_defect_roots, test_zero_residual_readback_reaches_owner_detailed_equilibrium, test_zero_residual_constructs_real_monotone_sinkhorn_step

### `tests/test_sinkhorn_rn_barrier_comparison_constructor.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_rn_barrier_comparison_has_theorem_backed_budget_constructor`
- What it does: Defines test_rn_barrier_comparison_has_theorem_backed_budget_constructor

### `tests/test_sinkhorn_zd_controlled_observer_equilibrium.py`

- Lines: `15`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_zd_controlled_observer_closes_sinkhorn_equilibrium_when_zd_vanishes`
- What it does: Defines test_zd_controlled_observer_closes_sinkhorn_equilibrium_when_zd_vanishes

### `tests/test_souriau_claimA_root_chain.py`

- Lines: `29`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `theorem_block, test_claimA_translator_inlines_partition_log_root_chain, test_souriau_partition_owner_root_is_definitional_log_partition_chain`
- What it does: Defines theorem_block, test_claimA_translator_inlines_partition_log_root_chain, test_souriau_partition_owner_root_is_definitional_log_partition_chain

### `tests/test_souriau_conformal_chiral_scale_bridge.py`

- Lines: `20`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_equilibrium_seed_bridge_to_zero_scale_semantic_packet_exists`
- What it does: Defines test_equilibrium_seed_bridge_to_zero_scale_semantic_packet_exists

### `tests/test_souriau_conformal_equilibrium_seed.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_souriau_conformal_equilibrium_seed_is_theorem_backed`
- What it does: Defines test_souriau_conformal_equilibrium_seed_is_theorem_backed

### `tests/test_souriau_first_variation_weyl_bridge.py`

- Lines: `18`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_souriau_first_variation_bridge_is_theorem_backed`
- What it does: Defines test_souriau_first_variation_bridge_is_theorem_backed

### `tests/test_souriau_kkt_exact_residual_translator.py`

- Lines: `36`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_translator_has_exact_residual_kkt_route, test_exact_residual_route_does_not_reintroduce_explicit_kkt_hypotheses, test_exact_residual_det_route_uses_no_bare_psd_packet`
- What it does: Defines test_translator_has_exact_residual_kkt_route, test_exact_residual_route_does_not_reintroduce_explicit_kkt_hypotheses, test_exact_residual_det_route_uses_no_bare_psd_packet

### `tests/test_souriau_metriplectic_square_translator.py`

- Lines: `34`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_square_dissipation_translator_branch_exists, test_square_dissipation_branch_removes_general_context_argument, test_square_dissipation_branch_has_no_fake_proof_stubs`
- What it does: Defines test_square_dissipation_translator_branch_exists, test_square_dissipation_branch_removes_general_context_argument, test_square_dissipation_branch_has_no_fake_proof_stubs

### `tests/test_souriau_operatorial_log_potential.py`

- Lines: `103`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, unittest`
- Classes: `SouriauOperatorialLogPotentialTests`
- What it does: Defines SouriauOperatorialLogPotentialTests

### `tests/test_souriau_thermodynamic_readout_seed_bridge.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_equilibrium_seed_constructs_thermodynamic_readout_stationarity`
- What it does: Defines test_equilibrium_seed_constructs_thermodynamic_readout_stationarity

### `tests/test_souriau_tomita_modular_flow_bridge.py`

- Lines: `67`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_souriau_tomita_modular_flow_bridge_is_source_owned, test_souriau_tomita_bridge_exposes_cyclic_standard_form_kms_owner_route, test_souriau_tomita_bridge_exposes_standard_form_owner_route, test_souriau_tomita_bridge_is_in_canonical_umbrella`
- What it does: Defines test_souriau_tomita_modular_flow_bridge_is_source_owned, test_souriau_tomita_bridge_exposes_cyclic_standard_form_kms_owner_route, test_souriau_tomita_bridge_exposes_standard_form_owner_route, test_souriau_tomita_bridge_is_in_canonical_umbrella

### `tests/test_souriau_translator_identity_balanced_stress.py`

- Lines: `15`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_translator_threads_identity_balanced_stress_constructor`
- What it does: Defines test_translator_threads_identity_balanced_stress_constructor

### `tests/test_souriau_weyl_partition.py`

- Lines: `105`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SouriauWeylPartitionTests`
- Top-level functions: `has_decl`
- What it does: Defines SouriauWeylPartitionTests, has_decl

### `tests/test_souriau_weyl_supertrace_corrected.py`

- Lines: `138`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `CorrectedSouriauWeylSupertraceTests`
- Top-level functions: `has_decl`
- What it does: Defines CorrectedSouriauWeylSupertraceTests, has_decl

### `tests/test_souriau_weyl_supertrace_layer.py`

- Lines: `88`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, re, unittest`
- Classes: `SouriauWeylSupertraceLayerTests`
- Top-level functions: `has_decl`
- What it does: Defines SouriauWeylSupertraceLayerTests, has_decl

### `tests/test_spin44_character_shadow.py`

- Lines: `28`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_spin44_character_shadow_is_explicitly_finite_shadow, test_spin44_character_shadow_exposes_weight_sum_formulas`
- What it does: Defines test_spin44_character_shadow_is_explicitly_finite_shadow, test_spin44_character_shadow_exposes_weight_sum_formulas

### `tests/test_strict_def.py`

- Lines: `148`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `StrictDefTests`
- Top-level functions: `_run_snippet, _combined_output, _extract_gap_json`
- What it does: Defines StrictDefTests, _run_snippet, _combined_output, _extract_gap_json

### `tests/test_strict_surface.py`

- Lines: `177`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `StrictSurfaceTests`
- Top-level functions: `_run_snippet, _combined_output, _extract_prefixed_json`
- What it does: Defines StrictSurfaceTests, _run_snippet, _combined_output, _extract_prefixed_json

### `tests/test_super_souriau_identity_balanced_stress.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `test_identity_balanced_stress_constructor_and_theorem_are_live_declarations`
- What it does: Defines test_identity_balanced_stress_constructor_and_theorem_are_live_declarations

### `tests/test_supercharge_transport_translation_packet.py`

- Lines: `86`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `SuperchargeTransportTranslationPacketTests`
- Top-level functions: `test_supercharge_transport_translation_packet_surface_exists, _run_snippet`
- What it does: Defines SuperchargeTransportTranslationPacketTests, test_supercharge_transport_translation_packet_surface_exists, _run_snippet

### `tests/test_supermetriplectic_bps_build.py`

- Lines: `24`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, subprocess, unittest`
- Classes: `SuperMetriplecticBPSBuildTests`
- What it does: Defines SuperMetriplecticBPSBuildTests

### `tests/test_supermetriplectic_cartan_bridge.py`

- Lines: `44`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticCartanBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticCartanBridgeTests, has_decl

### `tests/test_supermetriplectic_chiral_bridge.py`

- Lines: `49`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticChiralBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticChiralBridgeTests, has_decl

### `tests/test_supermetriplectic_chiral_scalar_closure.py`

- Lines: `47`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticChiralScalarClosureTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticChiralScalarClosureTests, has_decl

### `tests/test_supermetriplectic_drazin_bridge.py`

- Lines: `51`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticDrazinBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticDrazinBridgeTests, has_decl

### `tests/test_supermetriplectic_drazin_projector_constraint_bridge.py`

- Lines: `47`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticDrazinProjectorConstraintBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticDrazinProjectorConstraintBridgeTests, has_decl

### `tests/test_supermetriplectic_entropy_shadow_bridge.py`

- Lines: `43`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticEntropyShadowBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticEntropyShadowBridgeTests, has_decl

### `tests/test_supermetriplectic_inverse_bridge.py`

- Lines: `43`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticInverseBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticInverseBridgeTests, has_decl

### `tests/test_supermetriplectic_triad_bridge.py`

- Lines: `61`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `os, pathlib, re, subprocess, unittest`
- Classes: `SuperMetriplecticTriadBridgeTests`
- Top-level functions: `has_decl`
- What it does: Defines SuperMetriplecticTriadBridgeTests, has_decl

### `tests/test_theorem_significance.py`

- Lines: `522`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `json, pathlib, sys, tempfile, theorem_significance, unittest`
- Classes: `TheoremSignificanceTests`
- Top-level functions: `_decl`
- What it does: Defines TheoremSignificanceTests, _decl

### `tests/test_theory_shadow_representation.py`

- Lines: `40`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_theory_shadow_representation_statuses_are_explicit, test_theory_shadow_representation_delegates_to_owned_surfaces, test_theory_shadow_representation_has_no_fake_proof_stubs, test_theory_shadow_representation_is_imported_by_all`
- What it does: Defines test_theory_shadow_representation_statuses_are_explicit, test_theory_shadow_representation_delegates_to_owned_surfaces, test_theory_shadow_representation_has_no_fake_proof_stubs, test_theory_shadow_representation_is_imported_by_all

### `tests/test_thermodynamic_generator_equilibrium_seed_bridge.py`

- Lines: `12`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_thermodynamic_generator_uses_first_variation_stationarity_theorems`
- What it does: Defines test_thermodynamic_generator_uses_first_variation_stationarity_theorems

### `tests/test_thermodynamic_generator_first_variation_pair.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_thermodynamic_generator_exposes_readout_pair_from_first_variation`
- What it does: Defines test_thermodynamic_generator_exposes_readout_pair_from_first_variation

### `tests/test_triality_moe_aligned_owner_bound.py`

- Lines: `20`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_aligned_zd_bound_lives_on_owner_lane`
- What it does: Defines test_aligned_zd_bound_lives_on_owner_lane

### `tests/test_triality_moe_compressed_deviation_zero_constructor.py`

- Lines: `17`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_compressed_deviation_zero_route_is_theorem_backed`
- What it does: Defines test_compressed_deviation_zero_route_is_theorem_backed

### `tests/test_triality_moe_constructive_bound.py`

- Lines: `14`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_aligned_observer_uses_theorem_backed_bound`
- What it does: Defines test_aligned_observer_uses_theorem_backed_bound

### `tests/test_triality_moe_deviation_zero_constructive_bound.py`

- Lines: `18`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_deviation_zero_observer_uses_theorem_backed_bound`
- What it does: Defines test_deviation_zero_observer_uses_theorem_backed_bound

### `tests/test_triality_moe_deviation_zero_constructor_flow.py`

- Lines: `17`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_deviation_zero_constructor_exposes_zero_residual_flow_route`
- What it does: Defines test_deviation_zero_constructor_exposes_zero_residual_flow_route

### `tests/test_triality_moe_deviation_zero_owner_bound.py`

- Lines: `20`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_deviation_zero_zd_bound_lives_on_owner_lane`
- What it does: Defines test_deviation_zero_zd_bound_lives_on_owner_lane

### `tests/test_triality_moe_general_constructive_bound.py`

- Lines: `25`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_general_observer_defect_bound_is_theorem_backed`
- What it does: Defines test_general_observer_defect_bound_is_theorem_backed

### `tests/test_triality_moe_residual_zero_constructor_flow.py`

- Lines: `20`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_residual_zero_constructor_exposes_zero_residual_flow_route`
- What it does: Defines test_residual_zero_constructor_exposes_zero_residual_flow_route

### `tests/test_triality_moe_strain_zero_constructor_flow.py`

- Lines: `19`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_strain_zero_constructor_exposes_zero_residual_flow_route`
- What it does: Defines test_strain_zero_constructor_exposes_zero_residual_flow_route

### `tests/test_triality_moe_zd_controlled_constructor_flow.py`

- Lines: `18`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_zd_controlled_constructor_exposes_zero_residual_flow_route`
- What it does: Defines test_zd_controlled_constructor_exposes_zero_residual_flow_route

### `tests/test_ulam_trace_bridge.py`

- Lines: `109`
- AST status: `ok`
- CLI/entrypoint signals: `argparse`
- Imports: `argparse, json, pathlib, subprocess, sys, tools`
- Top-level functions: `_ulam_success, _ulam_failure, test_normalize_ulam_record_preserves_transition, test_run_bridge_writes_summary, test_ulam_trace_bridge_feeds_tactic_dataset, test_ulam_trace_bridge_cli`
- What it does: Defines _ulam_success, _ulam_failure, test_normalize_ulam_record_preserves_transition, test_run_bridge_writes_summary, test_ulam_trace_bridge_feeds_tactic_dataset

### `tests/test_vacuity_lint.py`

- Lines: `76`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, subprocess, tempfile, textwrap, unittest`
- Classes: `VacuityLintTests`
- Top-level functions: `_run_lint_snippet, _combined_output`
- What it does: Defines VacuityLintTests, _run_lint_snippet, _combined_output

### `tests/test_vacuity_planner.py`

- Lines: `978`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `collections, importlib, pathlib, sys, tools, types, typing, unittest`
- Classes: `VacuityPlannerTests`
- Top-level functions: `_load_planner_module`
- What it does: Defines VacuityPlannerTests, _load_planner_module

### `tests/test_vandermonde_root_chain.py`

- Lines: `37`
- AST status: `ok`
- Imports: `pathlib, re`
- Top-level functions: `live_decl, test_vandermonde_root_chain_is_mathlib_rooted_data_not_witness_packaging, test_vandermonde_consumers_use_data_names_not_witness_names`
- What it does: Defines live_decl, test_vandermonde_root_chain_is_mathlib_rooted_data_not_witness_packaging, test_vandermonde_consumers_use_data_names_not_witness_names

### `tests/test_weighted_weyl_equilibrium_bridge_theorems.py`

- Lines: `15`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_equilibrium_seed_now_forces_weighted_density_readout_to_pure_phase_axis_response, test_phase_axis_commuting_equilibrium_seed_now_kills_full_weighted_density_readout`
- What it does: Defines test_equilibrium_seed_now_forces_weighted_density_readout_to_pure_phase_axis_response, test_phase_axis_commuting_equilibrium_seed_now_kills_full_weighted_density_readout

### `tests/test_weyl_zero_scale_collapse.py`

- Lines: `11`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_zero_scale_structured_projector_hypotheses_have_theorem_backed_collapse`
- What it does: Defines test_zero_scale_structured_projector_hypotheses_have_theorem_backed_collapse

### `tests/test_weyl_zero_scale_semantic_packet.py`

- Lines: `11`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_zero_scale_semantic_packet_has_theorem_backed_zero_readout`
- What it does: Defines test_zero_scale_semantic_packet_has_theorem_backed_zero_readout

### `tests/test_winding_constructive_forcing.py`

- Lines: `17`
- AST status: `ok`
- Imports: `pathlib`
- Top-level functions: `test_has_clock_axis_forcing_seed_routes_through_cartan_grade_owner`
- What it does: Defines test_has_clock_axis_forcing_seed_routes_through_cartan_grade_owner

## `tools`

### `tools/__init__.py`

- Lines: `2`
- AST status: `ok`
- Imports: `tools`
- What it does: TIR (Tool-Integrated Reasoning) layer for the Info-Geometry Spire.

### `tools/alexandria/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Alexandria digestion and retrieval pipeline.

### `tools/alexandria/alexandria_algorithms.py`

- Lines: `422`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, hashlib, json, pathlib, typing`
- Classes: `AlexandriaGraph`
- Top-level functions: `stable_hash, read_jsonl, chunk_key_from_doc_id, canonical_entity_key, build_graph, anchor_seed_indices, neighbor_affinity, anchor_seeded_basins, basin_seed_score, detect_defects, defect_cost, component_docs, entity_overlay_docs, basin_edge_docs, write_jsonl, parse_args, main`
- What it does: Defines AlexandriaGraph, stable_hash, read_jsonl, chunk_key_from_doc_id, canonical_entity_key, build_graph

### `tools/alexandria/arango_ingest.py`

- Lines: `163`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, json, pathlib, sys, tools, typing, urllib`
- Top-level functions: `auth_header, request_json, sys_url, db_url, ensure_database, ensure_collection, ensure_index, iter_jsonl, import_rows, main`
- What it does: Defines auth_header, request_json, sys_url, db_url, ensure_database

### `tools/alexandria/automathtext_arango_ingest.py`

- Lines: `358`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, sys, tools, typing`
- Classes: `ImportPlanRow`
- Top-level functions: `iter_jsonl, count_jsonl, build_import_plan, validate_edge_endpoints, batched_jsonl, import_collection_batched, import_automath_graph, parse_args, main`
- What it does: Ingest AutoMathText-V2 Alexandria theorem-context JSONL into ArangoDB.

### `tools/alexandria/automathtext_v2_ingest.py`

- Lines: `1273`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, gzip, hashlib, json, math, pathlib, re, typing`
- Classes: `Fragment`
- Top-level functions: `stable_hash, load_jsonl, load_parquet, iter_rows, parse_meta, coerce_float, coerce_int, row_to_fragment, split_chunks, chunk_kind, normalized_entity, entity_type, extract_entities, theorem_like_score, proof_like_score, extract_binder_graph, write_jsonl, row_text`
- What it does: Convert AutoMathText-V2 shards/rows into Alexandria theorem-context graph JSONL.

### `tools/alexandria/conductive_context_to_lean_skeleton.py`

- Lines: `279`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, hashlib, json, pathlib, re, typing`
- Classes: `LeanCandidate`
- Top-level functions: `stable_hash, load_packet, sanitize_name, edge_terms, candidate_statement, candidates_from_packet, render_lean, render_markdown, write_json, main`
- What it does: Defines LeanCandidate, stable_hash, load_packet, sanitize_name, edge_terms, candidate_statement

### `tools/alexandria/download_automathtext_v2.py`

- Lines: `210`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, os, pathlib, typing`
- Classes: `DownloadPlan`
- Top-level functions: `normalize_config, pattern_for_config, build_allow_patterns, make_plan, import_huggingface_hub, write_json, read_token, list_manifest, run_download, parse_args, main`
- What it does: Defines DownloadPlan, normalize_config, pattern_for_config, build_allow_patterns, make_plan, import_huggingface_hub

### `tools/alexandria/fetch_arxiv_corpus.py`

- Lines: `335`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, gzip, io, pathlib, re, tarfile, urllib`
- Top-level functions: `strip_tex_comments, strip_tex_preamble, drop_tex_environments, strip_macro_definitions, clean_tex_braces, protect_math_segments, restore_math_segments, preserve_theorem_environments, preserve_math_environments, normalize_tex_commands, extract_arxiv_id, fetch_bytes, fetch_text, html_to_text, tex_to_text, try_extract_tex, download_arxiv_entry, parse_args`
- What it does: Defines strip_tex_comments, strip_tex_preamble, drop_tex_environments, strip_macro_definitions, clean_tex_braces

### `tools/alexandria/graph_context_rank.py`

- Lines: `534`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, os, pathlib, re, sys, typing`
- Top-level functions: `maybe_enable_gpu_backend, tokenize, read_jsonl, lexical_score, chunk_key_from_doc_id, entity_bonus, edge_symbol_tokens, query_overlap_gain, conductive_weight, build_graph, personalized_scores, scc_quotient_scores, edge_preview, activated_edges, query_abstraction_score, chunk_entity_terms, coarse_components, coarse_sccs`
- What it does: Defines maybe_enable_gpu_backend, tokenize, read_jsonl, lexical_score, chunk_key_from_doc_id

### `tools/alexandria/materialize_coarse_scc_overlay.py`

- Lines: `173`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, tools, typing`
- Top-level functions: `edge_preview, collect_entities_for_chunk, representative_terms, write_jsonl, materialize, main`
- What it does: Defines edge_preview, collect_entities_for_chunk, representative_terms, write_jsonl, materialize

### `tools/alexandria/proof_synthesis_report.py`

- Lines: `228`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, tools, typing`
- Top-level functions: `_text, execute_aql, flatten_witnesses, select_top_path, render_prompt, build_packet, write_outputs, main`
- What it does: Defines _text, execute_aql, flatten_witnesses, select_top_path, render_prompt

### `tools/alexandria/render_socratic_dossier.py`

- Lines: `97`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing`
- Top-level functions: `load_packet, render_hit, render_dossier, main`
- What it does: Defines load_packet, render_hit, render_dossier, main

### `tools/alexandria/repair_lineage.py`

- Lines: `301`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, subprocess, sys, time, typing`
- Classes: `GateResult, RepairAttempt`
- Top-level functions: `node_collection, node_key, arango_id, run_gate, purified_chunk_from_broken, build_repair_attempt, build_lineage_edges, append_jsonl, main`
- What it does: Defines GateResult, RepairAttempt, node_collection, node_key, arango_id, run_gate

### `tools/alexandria/retrieve_context.py`

- Lines: `96`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, re`
- Top-level functions: `tokenize, read_jsonl, score, main`
- What it does: Defines tokenize, read_jsonl, score, main

### `tools/alexandria/schema.py`

- Lines: `61`
- AST status: `ok`
- Imports: `__future__, hashlib, pathlib`
- Top-level functions: `stable_key, content_hash, infer_source_kind, source_uri`
- What it does: Defines stable_key, content_hash, infer_source_kind, source_uri

### `tools/alexandria/semantic_ingest.py`

- Lines: `492`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, hashlib, json, pathlib, re, typing`
- Classes: `Section, Chunk, Entity, Relation`
- Top-level functions: `stable_key, normalize_surface, detect_domain, tokenize, classify_chunk, split_sections, chunk_section_lines, corpus_stoplist, classify_surface, add_entity, extract_entities, relation_weight, extract_relations, digest_document, write_jsonl, main`
- What it does: Defines Section, Chunk, Entity, stable_key, normalize_surface, detect_domain

### `tools/alexandria/structural_chunking.py`

- Lines: `617`
- AST status: `ok`
- Imports: `__future__, ast, dataclasses, pathlib, re, tools, typing`
- Classes: `StructuralSection, StructuralChunk, ChunkingResult`
- Top-level functions: `tokenize, base_provenance, adjacent_edge, rebuild_adjacent_edges, structural_segments, cast_clone_chunk, content_hash_local, apply_cast_split_merge, looks_like_lean_ast, ast_token_text, ast_command_kind, ast_command_title, ast_command_text, chunk_lean_ast, latex_packet_title, chunk_latex, chunk_python_ast, split_sections`
- What it does: Defines StructuralSection, StructuralChunk, ChunkingResult, tokenize, base_provenance, adjacent_edge

### `tools/alexandria/txt2kg_hive_ingest.py`

- Lines: `1043`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, hashlib, json, pathlib, re, subprocess, sys, tempfile, tools, typing`
- Classes: `SourceRecord, ChunkRecord`
- Top-level functions: `canonical_json, stable_hash, short_key, write_json, write_jsonl, read_jsonl, iter_input_files, decode_text_file, extract_pdf_text, extract_text, chunk_text_txt2kg, source_kind_for, normalize_surface, extract_surfaces, surface_source, normalization_confidence, relation_type_for, heuristic_triples`
- What it does: Digest text libraries into retrieval-only KG triples and Hive tasks.

### `tools/alexandria/verify_automathtext_arango_descent.py`

- Lines: `338`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, sys, tools, typing`
- Classes: `QueryCheck`
- Top-level functions: `execute_aql, collection_count_query, collection_counts, edge_endpoint_check, structural_checks, positive_presence_checks, run_checks, make_live_runner, parse_args, main`
- What it does: Verify AutoMathText-V2 epistemic ancestry descent in ArangoDB.

### `tools/build_lock.py`

- Lines: `102`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, fcntl, json, os, pathlib, time, typing`
- Classes: `BuildLockBusyError, BuildLock`
- Top-level functions: `read_lock_metadata, acquire_build_lock`
- What it does: Defines BuildLockBusyError, BuildLock, read_lock_metadata, acquire_build_lock

### `tools/check_bipartite_bleed.py`

- Lines: `11`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/check_vacuity_policy.py`

- Lines: `168`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, tools`
- Top-level functions: `check_policy, main`
- What it does: Vacuity Policy Gate — Layer C of the vacuity enforcement system.

### `tools/classify_missing_all.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/docs/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Maintained documentation orchestration and generated status surfaces.

### `tools/docs/generate_auto_docs.py`

- Lines: `309`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, dataclasses, json, pathlib, tools, typing`
- Classes: `ModuleSummary`
- Top-level functions: `load_json, count_lean_files_and_loc, summarize_module, module_table_rows, seed_bridge_summary, frontier_names, burndown_names, compression_bundle_names, compression_module_names, frontier_names_matching, render_index, main`
- What it does: Defines ModuleSummary, load_json, count_lean_files_and_loc, summarize_module, module_table_rows, seed_bridge_summary

### `tools/docs/refresh_markdown_status.py`

- Lines: `267`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, dataclasses, os, pathlib`
- Classes: `StatusSpec`
- Top-level functions: `repo_markdown_files, all_candidate_markdown_files, should_manage, classify, relative_link, make_status_block, strip_existing_status, strip_inserted_status_block, rewrite_file, main`
- What it does: Defines StatusSpec, repo_markdown_files, all_candidate_markdown_files, should_manage, classify, relative_link

### `tools/docs/update_repo_docs.py`

- Lines: `333`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, subprocess, sys`
- Classes: `ExportSpec`
- Top-level functions: `run, ensure_exists, normalize_repo_relative, export_spec_for_paths, existing_export_specs, changed_tracked_lean_files, changed_export_specs, refresh_exports, current_export_paths, run_skynet, parse_args, main`
- What it does: Defines ExportSpec, run, ensure_exists, normalize_repo_relative, export_spec_for_paths, existing_export_specs

### `tools/extract_module_patch.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/failure_correction_driver.py`

- Lines: `795`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, os, pathlib, re, shlex, subprocess, typing`
- Classes: `CommandResult, RepairAttempt`
- Top-level functions: `parse_args, load_text, load_json, tail_text, extract_materialized_theorem_name, locate_materialized_block, replace_materialized_block, placeholder_reasons, capture_inline_value, capture_code_block, capture_section, normalize_yes_no, parse_reviewed_repair, run_capture, persist_output_from_stdout, format_external_command, render_creative_prompt, render_critical_prompt`
- What it does: Defines CommandResult, RepairAttempt, parse_args, load_text, load_json, tail_text

### `tools/find_scc.py`

- Lines: `54`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, base64, json, os, urllib`
- Top-level functions: `query, main`
- What it does: Defines query, main

### `tools/frontier/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Maintained semantic-export and frontier-analysis tooling.

### `tools/frontier/compiler_bridge_client.py`

- Lines: `564`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, re, sys, tools, typing`
- Classes: `CompilerBridgeSession`
- Top-level functions: `log_stage, server_command, normalize_result, infer_decl_position_in_text, resolve_bridge_position, build_rpc_invocation, call_bridge_method, parse_args, main`
- What it does: Defines CompilerBridgeSession, log_stage, server_command, normalize_result, infer_decl_position_in_text, resolve_bridge_position

### `tools/frontier/extract_module_patch.py`

- Lines: `599`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, math, matplotlib, networkx, os, pathlib, sys, typing`
- Top-level functions: `is_noise_decl, parse_args, default_out_paths, as_int, load_decl_meta, load_surface_rows, load_burndown, module_rows, row_priority, representative_rows, module_summary, neighbor_rows, extra_frontier_neighbors, seed_context_from_burndown, interface_edges, build_patch_graph, plot_patch_graph, render_markdown`
- What it does: Defines is_noise_decl, parse_args, default_out_paths, as_int, load_decl_meta

### `tools/frontier/proof_print.py`

- Lines: `108`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, time, tools`
- Top-level functions: `parse_args, main`
- What it does: Defines parse_args, main

### `tools/frontier/proof_runtime.py`

- Lines: `122`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, dataclasses, typing`
- Classes: `BridgeCallSpec`
- Top-level functions: `call_spec_for_print_mode, extract_print_text, build_prewarm_request, summarize_bridge_response`
- What it does: Defines BridgeCallSpec, call_spec_for_print_mode, extract_print_text, build_prewarm_request, summarize_bridge_response

### `tools/frontier/proof_session.py`

- Lines: `250`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, time, tools, typing`
- Top-level functions: `emit, parse_args, request_error, handle_request, main`
- What it does: Defines emit, parse_args, request_error, handle_request, main

### `tools/frontier/semantic_block_export.py`

- Lines: `496`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, queue, re, subprocess, sys, threading, time, tools`
- Classes: `JsonRpcError, LspClient`
- Top-level functions: `server_command, log_stage, inject_rpc_import, adjust_stable_id, adjust_pos, normalize_payload, fetch_semantic_blocks, export_semantic_blocks, parse_args, main`
- What it does: Defines JsonRpcError, LspClient, server_command, log_stage, inject_rpc_import, adjust_stable_id

### `tools/frontier/semantic_snapshot.py`

- Lines: `750`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, sys, time, tools, typing`
- Top-level functions: `log_stage, snapshot_server_command, inject_snapshot_imports, normalize_semantic_payload, normalize_bridge_payload, module_name_guess, first_error, call_rpc, build_snapshot, build_snapshot_sequential, build_snapshot_single_session, finalize_snapshot_payload, parse_args, main`
- What it does: Defines log_stage, snapshot_server_command, inject_snapshot_imports, normalize_semantic_payload, normalize_bridge_payload

### `tools/frontier/skynet_v2.py`

- Lines: `651`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, math, pathlib, re, tools, typing, urllib`
- Classes: `Edge, AuditFinding, SemanticWeb`
- Top-level functions: `semantic_json_paths, load_payload, normalize_source_file, parse_queue_audit, parse_unification_statuses, module_of_source_file, strongest_match, load_frontier_audits, block_decl_names, block_primary_tag_map, walk_neighbors, random_walk_with_restart, frontier_candidates, score_frontier_rows, unresolved_affects, render_markdown, parse_args, main`
- What it does: Defines Edge, AuditFinding, SemanticWeb, semantic_json_paths, load_payload, normalize_source_file

### `tools/generate_auto_docs.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_bridge_candidates.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_bridge_thinness_index.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_causal_report.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_debt_candidates.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_llm_debt_prompts.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_llm_frontier_prompts.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_self_optimization_report.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_source_sink_compression.py`

- Lines: `11`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_structural_dedup.py`

- Lines: `11`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_structural_fibers.py`

- Lines: `11`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_surrogate_index.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_unification_index.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/generate_vacuity_index.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/graph.py`

- Lines: `45`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, importlib, pathlib, types`
- Top-level functions: `_load_legacy_module`
- What it does: Compatibility shim for the archived declaration-graph wrapper.

### `tools/ig.py`

- Lines: `114`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, json, os, pathlib, subprocess, sys, time, uuid`
- Top-level functions: `generate_run_id, run_command, cmd_process, main`
- What it does: Info-Geometry Spire Orchestrator (IG-CLI)

### `tools/igf.py`

- Lines: `18`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, igf, pathlib, sys`
- What it does: Compatibility wrapper for the package-local igf CLI.

### `tools/infra/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Core maintenance and diagnostic infrastructure for the Spire.

### `tools/infra/aesop_tactic_prior.py`

- Lines: `154`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, re, typing`
- Top-level functions: `tactic_head, classify_tactic, annotate_jsonl, main`
- What it does: Aesop-inspired static tactic prior classification.

### `tools/infra/agentic_policy_lint.py`

- Lines: `219`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys, typing, yaml`
- Top-level functions: `_as_dict, _as_list, _must_contain, _load_yaml, _check_linkage, _check_runtime_policy, main`
- What it does: Defines _as_dict, _as_list, _must_contain, _load_yaml, _check_linkage

### `tools/infra/alchemical_loop.py`

- Lines: `68`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, datetime, json, pathlib, subprocess, sys`
- Top-level functions: `run_command, auto_promote, main`
- What it does: Defines run_command, auto_promote, main

### `tools/infra/analyze_stall_distributions.py`

- Lines: `164`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, typing`
- Top-level functions: `iter_jsonl, cone_bucket, ratio, run_analysis, main`
- What it does: Analyze bottlenecks in tactic path ranking telemetry.

### `tools/infra/analyze_tactic_path_ranking.py`

- Lines: `246`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, typing`
- Top-level functions: `iter_jsonl, _is_positive, _ranked_candidates, _topk_hit, _first_positive_rank, analyze_rows, _bucket, _rate, _summary_float, _rate_table, _recommendations, run_analysis, main`
- What it does: Analyze tactic path ranking datasets before reranker training.

### `tools/infra/apex_defect_profile.py`

- Lines: `874`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, time`
- Top-level functions: `load_sorry_set, _dominant_judgment, compute_shell_thinness, compute_singleton_shell_pressure, compute_witness_deficit, compute_non_owner_mediation, compute_skip_layer_density, compute_judgment_mismatch_density, compute_replacement_fragility, compute_boundary_load, find_non_owner_inventory, find_unsound_support, find_thin_shell_chokepoints, compute_suggested_read_order, collect_source_paths, discretize, severity_vector, _component_metadata`
- What it does: Apex-local defect profiler on the SCC-condensed declaration DAG.

### `tools/infra/arango_causal_chiral_cone_prompt.py`

- Lines: `483`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, tools, typing`
- Top-level functions: `arango_target, resolve_decl, traverse_cone, component_members, overlay_rows, node_name, add_source_excerpts, render_markdown, build_packet, main`
- What it does: Emit a causal/chiral cone prompt packet for one Lean declaration.

### `tools/infra/arango_dag_algorithms.py`

- Lines: `2288`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, hashlib, json, networkx, pathlib, sys, time, typing, urllib`
- Classes: `QuotientGraph`
- Top-level functions: `layer_depth, flow_polarity, process_dependency_role, process_boundary_class, process_locality_class, process_defect_tags, defect_cost, layer_histogram_to_array, run_aql, load_quotient_graph, topo, bfs_dist, dag_longest_depth_with_pred, dag_longest_depth, path_counts, dominator_counts, dominator_masks, stable_hash`
- What it does: Run DAG graph algorithms over the live Arango topology overlay.

### `tools/infra/arango_env.py`

- Lines: `43`
- AST status: `ok`
- Imports: `__future__, igf, os, pathlib, sys`
- What it does: Compatibility wrapper for shared Arango environment loading.

### `tools/infra/arango_fidelity_audit.py`

- Lines: `171`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, json, os, pathlib, tools, typing, urllib`
- Top-level functions: `count_jsonl, load_json, arango_collection_count, build_report, parse_args, main`
- What it does: Audit how faithful the current Arango graph is to local graph artifacts.

### `tools/infra/arango_gravity_context.py`

- Lines: `1410`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, igf, json, math, pathlib, re, sys, tools, typing, urllib`
- Top-level functions: `tokenize, token_text, query_phrases, load_equivalence_components, expand_query_tokens, read_jsonl, arango_cursor_all, load_arango, _arango_doc_id, _edge_endpoint_key, normalize_raw_node, normalize_raw_edge, node_rep_layer, node_rep_depth, node_rep_depth_slug, node_rep_layer_description, rep_layer_counts, load_faithful_arango`
- What it does: Build Lean-grounded "gravitational" context from the proven declaration graph.

### `tools/infra/arango_layered_ingest.py`

- Lines: `290`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, dataclasses, json, os, pathlib, tools, typing, urllib`
- Classes: `CollectionSpec, ArangoTarget`
- Top-level functions: `auth_header, request_json, db_url, ensure_database, list_collections, create_collection, truncate_collection, iter_jsonl, import_batch, import_jsonl_batched, collection_count, main`
- What it does: Ingest hydrated raw graph and topology overlay JSONL into ArangoDB.

### `tools/infra/arango_raw_infotree_graph.py`

- Lines: `303`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, arango_raw_infotree_ingest, argparse, dataclasses, json, os, pathlib, sys, tools, typing, urllib`
- Classes: `GraphProbe`
- Top-level functions: `graph_url, graph_exists, drop_graph, create_graph, named_graph_counts, networkx_probe, parse_args, main`
- What it does: Create/probe a named ArangoDB graph for raw_infotree_* collections.

### `tools/infra/arango_raw_infotree_ingest.py`

- Lines: `1011`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, dataclasses, json, os, pathlib, subprocess, sys, tools, typing, urllib`
- Classes: `CollectionSpec, ArangoTarget`
- Top-level functions: `auth_header, request_json, db_url, sys_url, ensure_database, list_collections, create_collection, ensure_index, ensure_indexes, truncate_collection, drop_collection, collection_count, iter_jsonl, count_jsonl, prefixed_key, normalize_row, stable_row_hash, import_batch`
- What it does: Ingest stage raw_infotree_* JSONL exports into ArangoDB.

### `tools/infra/arango_structural_vacuity_audit.py`

- Lines: `460`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, base64, collections, datetime, json, os, pathlib, re, sys, tools, urllib`
- Top-level functions: `collection_name, positive_int, request_json, run_aql, build_query, make_report, write_json, md_code, write_markdown, parse_args, main`
- What it does: Defines collection_name, positive_int, request_json, run_aql, build_query

### `tools/infra/aria_concept_graph.py`

- Lines: `312`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, sys, tools, typing`
- Classes: `ConceptNode, DependencyGraph`
- Top-level functions: `slug, normalize_phrase, concept_kind, extract_concepts, concept_edges, build_dependency_graph, ground_concept, build_concept_graph, main`
- What it does: Aria-style concept graph builder over local LeanSearch records.

### `tools/infra/aria_scorer_lite.py`

- Lines: `151`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, re, sys, tools, typing`
- Top-level functions: `load_record_names, extract_lean_identifiers, grounded_terms, score_alignment, main`
- What it does: Local AriaScorer-lite semantic grounding report.

### `tools/infra/artifacts.py`

- Lines: `127`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, datetime, json, pathlib, typing`
- Top-level functions: `normalize_repo_output, load_json_dict, load_decl_index_meta, meta_matches_decl_refresh, should_skip_decl_refresh, stamp_decl_index_meta, find_missing_decl_source_files`
- What it does: Defines normalize_repo_output, load_json_dict, load_decl_index_meta, meta_matches_decl_refresh, should_skip_decl_refresh

### `tools/infra/autonomous_math/__init__.py`

- Lines: `2`
- AST status: `ok`
- What it does: Autonomous mathematician pipeline modules.

### `tools/infra/autonomous_math/compiler_loop.py`

- Lines: `33`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, dataclasses, pathlib, subprocess, typing`
- Classes: `CompileResult`
- Top-level functions: `close`
- What it does: Compiler/proof repair loop surface.

### `tools/infra/autonomous_math/evidence_packet.py`

- Lines: `167`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, dataclasses, typing`
- Classes: `EvidenceClaim, FormalizationTarget, EvidencePacket`
- Top-level functions: `from_dict, _confidence_bucket, from_deep_research_state`
- What it does: Typed evidence packet used between research and formalization phases.

### `tools/infra/autonomous_math/lean_coder.py`

- Lines: `47`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, pathlib, typing`
- Top-level functions: `write_scaffold`
- What it does: Lean coder stage.

### `tools/infra/autonomous_math/lean_designer.py`

- Lines: `64`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, re, typing`
- Top-level functions: `_slug, synthesize`
- What it does: Lean theorem-design synthesizer.

### `tools/infra/autonomous_math/memory_ingest.py`

- Lines: `26`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, evidence_packet, json, pathlib, typing`
- Top-level functions: `ingest`
- What it does: Memory ingestion stage for autonomous_math pipeline.

### `tools/infra/autonomous_math/pauli_auditor.py`

- Lines: `57`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, typing`
- Top-level functions: `_admissible, audit`
- What it does: Pauli-style admissibility audit.

### `tools/infra/autonomous_math/research_controller.py`

- Lines: `582`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, os, pathlib, sys, tools, typing`
- Top-level functions: `_make_client, _slug, parse_args, _parse_allowed_sources, _parse_mcp_servers, _claims_cited, main`
- What it does: End-to-end autonomous mathematician controller (first production lane).

### `tools/infra/autonomous_math/socratic_engine.py`

- Lines: `40`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, evidence_packet, typing`
- Top-level functions: `expand`
- What it does: Socratic/Jungian expansion over evidence packet.

### `tools/infra/autonomous_math/socratic_packet.py`

- Lines: `200`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, evidence_packet, re, typing`
- Top-level functions: `_extract_tagged_block, _theorem_targets, build_packet_from_loop`
- What it does: Packetize Socratic alchemy loop outputs into the autonomous_math evidence format.

### `tools/infra/batch_raw_infotree_export.py`

- Lines: `368`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, shutil, subprocess, sys, time, typing`
- Classes: `FileResult`
- Top-level functions: `tail_text, safe_slug, olean_path_for, iter_jsonl, jsonl_count, discover_files, validate_export, export_one, merge_valid_exports, parse_args, main`
- What it does: Batch RawInfoTree export with LeanDojo-style safety gates.

### `tools/infra/blueprint_alexandria_bridge.py`

- Lines: `187`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, sys, tools, typing`
- Top-level functions: `iter_jsonl, stable_hash, slug, suggested_lean_name, load_entities, candidate_decls, build_nodes, write_jsonl, main`
- What it does: Build Blueprint-style formalization nodes from Alexandria paper artifacts.

### `tools/infra/blueprint_arango_match.py`

- Lines: `117`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, tools, typing`
- Top-level functions: `iter_jsonl, node_query, match_node, write_jsonl, main`
- What it does: Match Blueprint-style nodes to repo declarations and cone seeds.

### `tools/infra/build.py`

- Lines: `222`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, hashlib, os, pathlib, subprocess, sys, tools, typing`
- Top-level functions: `log_spectral_stage, compute_olean_content_hash, compute_lean_source_hash, run_locked_lake_build, ensure_built_executable, build_indexer_command, run_locked_prebuild`
- What it does: Defines log_spectral_stage, compute_olean_content_hash, compute_lean_source_hash, run_locked_lake_build, ensure_built_executable

### `tools/infra/build_changed_lean.py`

- Lines: `156`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, subprocess, sys, typing`
- Top-level functions: `run_git, changed_paths, path_to_module, collect_modules, parse_args, main`
- What it does: Defines run_git, changed_paths, path_to_module, collect_modules, parse_args

### `tools/infra/build_chiral_patch_hashes.py`

- Lines: `705`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, hashlib, json, networkx, numpy, os, pathlib, re, scipy`
- Classes: `PatchRun, ChiralPatch, PatchMember, PatchEdge, SpectralSignature`
- Top-level functions: `stable_key, doc_id, patch_doc_id, normalize_node_key, hash_input_files, compute_spectral_signature, cartan_proxy_sector, dominant_cartan_sector, compute_chiral_metrics, fingerprint_bucket, fingerprint_features, build_patch_dependency_edges, build_patches, main`
- What it does: Build conservative chiral patches over the declaration graph.

### `tools/infra/build_claim_packet.py`

- Lines: `54`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `json, pathlib, sys`
- Top-level functions: `create_packet, main`
- What it does: Defines create_packet, main

### `tools/infra/build_link_ats_dataset.py`

- Lines: `737`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, hashlib, json, math, pathlib, random, typing`
- Classes: `DeclMeta, TypeMeta, FailurePair, PosEdge`
- Top-level functions: `_iter_jsonl, _stable_float_01, _split_for, _normalize_kind, _module_family, _truncate, _load_surface_categories, _load_decls, _load_rep_depth, _load_types, _load_positive_edges, _load_failures, _build_non_edges, _sample_random_negative_dst, _pair_key, _compute_unusual_score, _decl_payload, parse_args`
- What it does: Defines DeclMeta, TypeMeta, FailurePair, _iter_jsonl, _stable_float_01, _split_for

### `tools/infra/build_mcbal_library.py`

- Lines: `293`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, html, json, pathlib, re, typing`
- Top-level functions: `strip_tags_keep_breaks, extract_title, extract_updated_and_read_time, parse_human_date, extract_headings, extract_links, keyword_profile, top_nonzero, write_post_markdown, run, main`
- What it does: Build a structured local library from downloaded mcbal blog HTML files.

### `tools/infra/build_predigestion_packets.py`

- Lines: `214`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, typing`
- Top-level functions: `canonical_json, stable_hash, require_enum, iter_jsonl, first_string, list_of_strings, default_claim, infer_risk, make_packet, write_jsonl, build_packets, summary_for, main`
- What it does: Build non-authoritative predigestion claim packets from source chunks.

### `tools/infra/build_state_first_lane.py`

- Lines: `58`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys`
- Top-level functions: `parse_args, main`
- What it does: Defines parse_args, main

### `tools/infra/build_tactic_path_ranking_dataset.py`

- Lines: `551`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, math, pathlib, re, typing`
- Top-level functions: `iter_jsonl, stable_hash, split_for, normalize_goal, decision_key, tactic_family, edge_type_for, failure_label, stall_type_for, operator_score, count_local_hypotheses, quantifier_depth, token_count, hodge_harmonic_signal, chiral_flow_direction, _empty_frequency_stats, build_frequency_stats, add_entropic_weights`
- What it does: Build operator-informed tactic path ranking rows from tactic telemetry.

### `tools/infra/build_tactic_training_dataset.py`

- Lines: `702`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, hashlib, json, pathlib, re, sys, tools, typing`
- Classes: `SuccessTransition, FailureTransition`
- Top-level functions: `iter_jsonl, iter_json_docs, stable_hash, normalize_goal, goal_hash, split_for, tactic_family, lean_output_from_verification, leandojo_successes, hive_successes, hive_failures, leantrail_failures, real_prover_successes, jixia_successes, ulam_successes, ulam_failures, sft_row, failure_row`
- What it does: Build canonical tactic SFT/DPO/failure datasets from local telemetry.

### `tools/infra/candidate_bridge_packet.py`

- Lines: `290`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, re, sys, typing`
- Top-level functions: `utc_now, slug, _uniq, load_json, write_json, default_forbidden_moves, build_packet, validate_packet, cmd_build, cmd_validate, parse_args, main`
- What it does: Candidate-bridge packet builder + validator.

### `tools/infra/canonical_policy_lint.py`

- Lines: `462`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, re, sys, typing`
- Classes: `PropSurface, PublicTheorem, SuspectTheorem`
- Top-level functions: `normalize_decl_file, coerce_line, load_json, surface_key, suspect_key, load_jsonl, read_file_lines, has_valid_source_line, theorem_is_private, theorem_class_tag, theorem_block, theorem_has_trivial_proof, scan_prop_surfaces, scan_public_theorems, scan_suspect_theorems, theorem_has_weak_graph_support, main`
- What it does: ⚖️ THE PAULI CANONICAL POLICY LINTER (Authority-Grounded)

### `tools/infra/causal_chiral_prompt_builder.py`

- Lines: `349`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, re, sys, typing`
- Top-level functions: `iter_jsonl, load_decl_index, load_expr_fingerprints, repo_path, source_excerpt, weak_cone_bfs, shell_sample, resolve_apex, expr_context, render_prompt, build_packet, main`
- What it does: Defines iter_jsonl, load_decl_index, load_expr_fingerprints, repo_path, source_excerpt

### `tools/infra/causal_cone_spectrum.py`

- Lines: `1193`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, time, typing`
- Top-level functions: `_iter_component_members, _require_components, _strict_int_list, _strict_int, load_decl_index, load_structure, _extract_arango_payload, load_structure_from_arango, load_depth_tags, load_depth_tags_from_arango, verify_edge_pair_consistency, verify_edge_semantics, past_cone_bfs, forward_cone_bfs, shell_decomposition, component_signature, precompute_signatures, component_own_parities`
- What it does: Causal-cone diagnostics on the SCC-condensed declaration DAG.

### `tools/infra/changed_verify.py`

- Lines: `182`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, subprocess, sys`
- Top-level functions: `parse_args, changed_lean_files, run_file_gate, umbrella_target, main`
- What it does: Defines parse_args, changed_lean_files, run_file_gate, umbrella_target, main

### `tools/infra/check_bipartite_bleed.py`

- Lines: `723`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json, ordered_unique, component_repr, sort_component_ids, parse_structure, parse_bipartite, closure_from_component, downward_closure, shared_strict_dominator_ids, support_summary, find_anchor_candidates, pairwise_bleed_scan, summarize_violations, anchor_status_index, selector_score, build_structural_hotspots, render_hotspots_markdown`
- What it does: Defines parse_args, load_json, ordered_unique, component_repr, sort_component_ids

### `tools/infra/check_gauge_obstruction_tags.py`

- Lines: `389`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, sys, typing`
- Classes: `DeclarationHit`
- Top-level functions: `parse_args, normalize_signature, split_signature_and_conclusion, classify_declaration, extract_hits, file_tag, to_json, write_markdown, _normalize_prefix, _matches_prefix, run_policy_check, main`
- What it does: Defines DeclarationHit, parse_args, normalize_signature, split_signature_and_conclusion, classify_declaration, extract_hits

### `tools/infra/check_hollow_theorems.py`

- Lines: `272`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, datetime, json, os, pathlib, re, sys, typing`
- Top-level functions: `detect_trivial_identity, detect_assumption_echo, detect_vacuous_premise, detect_semantic_mismatch, score_hollow_node, is_generated_lemma, run_fidelity_audit, write_reports, main`
- What it does: ⚖️ THE PAULI AUDITOR: Semantic Fidelity & Hollow Theorem Detector.

### `tools/infra/check_representation_depth.py`

- Lines: `458`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_jsonl, normalize_decls, classify_edge, aggregate_edges, summarize, render_md, main`
- What it does: Defines parse_args, load_jsonl, normalize_decls, classify_edge, aggregate_edges

### `tools/infra/check_research_handoff_gate.py`

- Lines: `66`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys, tools`
- Top-level functions: `check_nemoclaw_note, parse_args, main`
- What it does: ClawCode handoff gate for research-packet + NemoClaw provenance note.

### `tools/infra/check_resident_model_endpoint.py`

- Lines: `229`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing, urllib`
- Top-level functions: `http_json, model_ids, yaml_scalar_after, block_bounds, hermes_default, nemoclaw_lane_model, chat_probe_payload, run_check, main`
- What it does: Check the resident local model endpoint and config alignment.

### `tools/infra/check_semantic_flow_report.py`

- Lines: `196`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, subprocess, sys, typing`
- Top-level functions: `parse_args, require, run_generate, main`
- What it does: Defines parse_args, require, run_generate, main

### `tools/infra/check_vllm_mistral_compat.py`

- Lines: `158`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, importlib, json, pathlib, subprocess, typing`
- Top-level functions: `run_help, vllm_package_root, source_text_under, source_marker_report, check_compat, main`
- What it does: Check local vLLM CLI compatibility for Mistral-family serving.

### `tools/infra/claim_promote.py`

- Lines: `116`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, os, requests, sys, typing`
- Classes: `Arango`
- Top-level functions: `now_iso, env, main`
- What it does: Phase-1 claim promotion guard.

### `tools/infra/classify_missing_all.py`

- Lines: `185`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, json, pathlib, re, typing`
- Top-level functions: `load_json, first_namespace, classify, render_md, main`
- What it does: Defines load_json, first_namespace, classify, render_md, main

### `tools/infra/dag_all.py`

- Lines: `81`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, subprocess, sys`
- Top-level functions: `parse_args, step_command, main`
- What it does: Defines parse_args, step_command, main

### `tools/infra/dag_config.py`

- Lines: `169`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, dataclasses, os, pathlib, tools, typing`
- Classes: `DagBuildConfig, DagAuthoritativeArtifacts, DagDerivedReports, DagCoveragePolicy, DagLeakagePolicy, DagPolicies, DagToolchainConfig`
- Top-level functions: `_require_str, _require_int, _require_dict, _resolve_repo_path, resolve_dag_toolchain_path, repo_display_path, load_dag_toolchain_config`
- What it does: Defines DagBuildConfig, DagAuthoritativeArtifacts, DagDerivedReports, _require_str, _require_int, _require_dict

### `tools/infra/dag_doctor.py`

- Lines: `472`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, os, pathlib, shutil, sys, typing`
- Classes: `CheckResult`
- Top-level functions: `parse_args, parse_iso_timestamp, format_age, file_mtime, extract_graph_coverage, add, has_result, suggestion_lines, process_exists, writable_directory, preferred_matplotlib_dir, main`
- What it does: Defines CheckResult, parse_args, parse_iso_timestamp, format_age, file_mtime, extract_graph_coverage

### `tools/infra/dag_manifest.py`

- Lines: `178`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, subprocess, sys, typing`
- Top-level functions: `parse_args, _file_info, _manifest_path, _coverage_summary, main`
- What it does: Defines parse_args, _file_info, _manifest_path, _coverage_summary, main

### `tools/infra/dag_refresh.py`

- Lines: `101`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, subprocess, sys`
- Top-level functions: `parse_args, main`
- What it does: Defines parse_args, main

### `tools/infra/dag_reports.py`

- Lines: `113`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, os, pathlib, subprocess, sys, time`
- Top-level functions: `parse_args, resolve_step_command, build_report_env, main`
- What it does: Defines parse_args, resolve_step_command, build_report_env, main

### `tools/infra/dag_status.py`

- Lines: `234`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, pathlib, sys, typing`
- Top-level functions: `parse_args, parse_iso_timestamp, format_age, format_sync, file_mtime, extract_graph_coverage, top_label, timing_summary, main`
- What it does: Defines parse_args, parse_iso_timestamp, format_age, format_sync, file_mtime

### `tools/infra/debug_gravity.py`

- Lines: `1168`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, collections, json, math, os, pathlib, re, sys, typing, urllib`
- Top-level functions: `repo_root_from, tokenize, token_text, query_phrases, load_equivalence_components, expand_query_tokens, read_jsonl, arango_request, add_arango_auth, arango_cursor_all, load_arango, _arango_doc_id, _edge_endpoint_key, normalize_raw_node, normalize_raw_edge, node_rep_layer, node_rep_depth, node_rep_depth_slug`
- What it does: Build Lean-grounded "gravitational" context from the proven declaration graph.

### `tools/infra/decl_graph.py`

- Lines: `316`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, collections, json, math, networkx, pathlib, typing`
- Top-level functions: `normalize_repo_relative, load_decl_meta, load_surface_categories, build_declaration_graph, dominant_category, build_module_graph, load_decl_graph_bundle, filter_declaration_graph_by_surface, module_strength_rows, select_plot_subgraph, replaceable_surface_mass, support_pressure, dominant_pressure, primary_action, burn_down_rows, annotate_hotspot_graph`
- What it does: Defines normalize_repo_relative, load_decl_meta, load_surface_categories, build_declaration_graph, dominant_category

### `tools/infra/decl_graph_support.py`

- Lines: `166`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, collections, dataclasses, json, math, os, pathlib, sys, tools, typing`
- Top-level functions: `load_jsonl, parse_decl_attrs, structural_role_for_profile, load_decl_graph, weak_graph_evidence`
- What it does: ⚖️ THE PAULI DECLARATION GRAPH SUPPORT

### `tools/infra/deep_research/__init__.py`

- Lines: `11`
- AST status: `ok`
- What it does: Official-pattern deep research controller package.

### `tools/infra/deep_research/brief_rewriter.py`

- Lines: `102`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, common, json, typing`
- Top-level functions: `_normalize_list, normalize_research_brief, rewrite_research_brief`
- What it does: Research-brief rewrite stage for deep research controller.

### `tools/infra/deep_research/clarifier.py`

- Lines: `83`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, common, json, typing`
- Top-level functions: `normalize_clarification, clarify_goal`
- What it does: Clarification stage for deep research controller.

### `tools/infra/deep_research/common.py`

- Lines: `63`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, datetime, json, pathlib, re, typing`
- Top-level functions: `utc_now, to_dict, output_text, parse_json_text, load_json, write_json`
- What it does: Shared utilities for deep research controller.

### `tools/infra/deep_research/controller.py`

- Lines: `486`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, os, pathlib, sys, tools, typing`
- Top-level functions: `_make_client, _slug, _parse_allowed_sources, _parse_mcp_servers, _ensure_claim_citations, _required_subquestions_covered, parse_args, main`
- What it does: Official-pattern deep research controller.

### `tools/infra/deep_research/planner.py`

- Lines: `114`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, common, json, typing`
- Top-level functions: `_normalize_sources, normalize_plan, create_plan`
- What it does: Planner stage for deep research controller.

### `tools/infra/deep_research/retriever.py`

- Lines: `211`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, common, json, typing`
- Top-level functions: `build_tools, _collect_urls, normalize_finding, research_subquestion`
- What it does: Retriever/reader stage for deep research controller.

### `tools/infra/deep_research/verifier.py`

- Lines: `126`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, common, json, typing`
- Top-level functions: `normalize_verdict, verify_research`
- What it does: Verifier stage for deep research controller.

### `tools/infra/deep_research/writer.py`

- Lines: `55`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, common, json, typing`
- Top-level functions: `synthesize_report`
- What it does: Writer stage for deep research controller.

### `tools/infra/dgx_spark_hybrid_orchestrator.py`

- Lines: `635`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, pathlib, subprocess, sys, time, tools, typing`
- Classes: `StepResult`
- Top-level functions: `_utc_now, _utc_stamp, _resolve_profile_value, _write_text, _run_step, parse_args, _python, main, _finalize_manifest`
- What it does: Defines StepResult, _utc_now, _utc_stamp, _resolve_profile_value, _write_text, _run_step

### `tools/infra/dual_hypothesis_sampler.py`

- Lines: `535`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, hashlib, json, pathlib, random, re, subprocess, sys, typing`
- Classes: `ContextChunk`
- Top-level functions: `_utc_now, _stamp, _slug, _tokenize, _safe_read, _extract_lean_code, _json_post, _normalize_chat_base_url, _chat_completion, _sanitize_gemini_args, _messages_to_prompt, _gemini_cli_completion, _load_black_books, _load_context_files, _load_dag_context, _build_messages, parse_args, main`
- What it does: Defines ContextChunk, _utc_now, _stamp, _slug, _tokenize, _safe_read

### `tools/infra/enrich_tactic_path_operator_spectrum.py`

- Lines: `493`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, math, pathlib, typing`
- Top-level functions: `iter_jsonl, write_jsonl, stable_hash, safe_float, clamp01, tactic_family, is_positive, stall_type, is_stall, candidate_score, candidate_base_weight, repeated_family_pressure, row_feature, compute_operator_spectrum, enrich_candidate, decision_point_key, aggregate_decision_point_rows, enrich_row`
- What it does: Enrich tactic path-ranking rows with local operator-spectrum proxies.

### `tools/infra/enrich_tactic_path_with_lightcone_spectrum.py`

- Lines: `315`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, math, pathlib, typing`
- Top-level functions: `iter_jsonl, stable_hash, clamp01, safe_float, load_spectral_report, normalize_node_scores, context_for, candidate_anchor_names, score_for_candidate, enrich_candidate, infer_apex, enrich_rows, write_jsonl, main`
- What it does: Attach local lightcone spectral diagnostics to tactic path-ranking rows.

### `tools/infra/epistemic_reactor_ensemble.py`

- Lines: `455`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, pathlib, re, sys, typing, urllib`
- Top-level functions: `canonical_json, stable_hash, read_json, write_json, write_jsonl, parse_temperatures, samples_per_temperature, consensus_threshold, compact_context, render_prompt, normalize_claim, candidate_key, edge_component_key, heuristic_candidates, parse_llm_candidates, openai_compatible_candidates, sample_once, build_consensus`
- What it does: Run side-effect-free LLM ensemble infusion over a compressed cone packet.

### `tools/infra/export_public_release.py`

- Lines: `310`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, os, pathlib, re, shutil, subprocess, tempfile, typing`
- Classes: `PathAudit`
- Top-level functions: `run, parse_excludes, gather_stats, iter_text_lines, sample_license_hits, write_stub, write_index, checksums, main`
- What it does: Defines PathAudit, run, parse_excludes, gather_stats, iter_text_lines, sample_license_hits

### `tools/infra/external_proof_correspondence.py`

- Lines: `102`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing`
- Top-level functions: `read_jsonl, classify, plan_for, parse_args, main`
- What it does: Derive Lean adapter/reconstruction plans from ExternalTheoremCandidatePacket batches.

### `tools/infra/external_theorem_harvester.py`

- Lines: `520`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, html, json, pathlib, re, sys, typing, urllib, xml`
- Top-level functions: `normalize_source_system, iter_files, query_terms, matches_query, default_imports, default_symbol_map, classify, module_name_for, parse_local_declarations, text_from_html, fetch_text, absolutize_url, parse_logipedia_search_or_detail, parse_afp_entry_pages, fetch_arxiv, namespace_from_module, build_packet, write_outputs`
- What it does: Harvest external theorem-intelligence packets from local formal-library mirrors or arXiv.

### `tools/infra/external_theorem_ingest.py`

- Lines: `126`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, typing`
- Top-level functions: `read_records, validate_records, write_outputs, parse_args, main`
- What it does: Normalize, validate, and split External Theorem Hive packet batches.

### `tools/infra/extract_compressed_cone.py`

- Lines: `392`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, sys, tools, typing`
- Top-level functions: `stable_hash, component_id, component_key, compact_component, dedup_component_edges, group_member_counts, build_ensemble_payload, shadow_merge_template, parse_temperatures, build_packet, render_markdown, main`
- What it does: Extract an SCC-compressed causal cone packet for LLM ensemble infusion.

### `tools/infra/extract_expr_fingerprints.py`

- Lines: `158`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, typing`
- Top-level functions: `sha256_hex, tokenize, binder_depth_proxy, split_name_atoms, redex_proxy, kind_one_hot, process_decl, iter_jsonl, main`
- What it does: Build lightweight declaration-side ExprFingerprint proxies from decls.jsonl.

### `tools/infra/find_vacuous.py`

- Lines: `66`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `igf, json, pathlib, sys, tools`
- Top-level functions: `run_aql, main`
- What it does: Defines run_aql, main

### `tools/infra/gemini_account_adapter.py`

- Lines: `162`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, subprocess, sys, typing`
- Top-level functions: `utc_now, sanitize_gemini_args, build_prompt, run_gemini, main`
- What it does: Account-auth Gemini CLI adapter for single-segment ideation.

### `tools/infra/gemini_cli_guard.py`

- Lines: `172`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, random, sys, time, typing`
- Top-level functions: `load_state, write_state, recent_events, evaluate, parse_args, main`
- What it does: Rate-limit explicit Gemini CLI use for the theorem-factory workflow.

### `tools/infra/generate_black_books_keyword_report.py`

- Lines: `322`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, json, os, pathlib, re, subprocess`
- Classes: `CorpusDoc`
- Top-level functions: `parse_args, git_head, list_tracked_markdown, tokenize, iter_docs, build_term_index, top_docs_by_mass, ensure_parent, render_markdown, main`
- What it does: Build a full lexical index from black-book markdown files only.

### `tools/infra/generate_black_books_story_from_keyword_index.py`

- Lines: `365`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, datetime, json, math, pathlib, re, subprocess`
- Top-level functions: `parse_args, git_head, load_json, pick_terms, load_docs, deep_search_excerpts, cluster_terms, render_story, ensure_parent, main`
- What it does: Create a black-books story from full black-books keyword index.

### `tools/infra/generate_causal_report.py`

- Lines: `200`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, re, sys, typing`
- Top-level functions: `strip_lean_comments, declaration_bearing_files, indexed_files, graph_coverage, main`
- What it does: ⚖️ THE PAULI CAUSAL AUDITOR (ArangoDB SCC-Grounded)

### `tools/infra/generate_equivalence_dictionary.py`

- Lines: `825`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, datetime, json, pathlib, re, sys, typing`
- Top-level functions: `parse_args, now_utc_iso, module_name_from_path, qualify_name, push_namespace, pop_namespace, find_top_level_colon, split_top_level_op, leading_identifier, first_identifier, short_name, resolve_head, resolve_head_with_status, is_probable_local_head, parse_decl_header, normalize_curated_path, load_curated_relations, scan_lean_files`
- What it does: Defines parse_args, now_utc_iso, module_name_from_path, qualify_name, push_namespace

### `tools/infra/generate_expr_alpha_dedup.py`

- Lines: `466`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, datetime, hashlib, json, pathlib, sys, typing`
- Top-level functions: `utc_now_iso, parse_args, iter_jsonl, parse_key, stable_hash, role_sort_key, node_payload, rel_path, build_markdown, build_missing_input_markdown, main`
- What it does: Defines utc_now_iso, parse_args, iter_jsonl, parse_key, stable_hash

### `tools/infra/generate_hypothesis_debt_report.py`

- Lines: `406`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, math, pathlib, re, statistics, sys, typing`
- Classes: `DeclDebtRow`
- Top-level functions: `parse_args, normalize_target_path, load_targets, find_signature_end, find_top_level_colon, split_names, is_hypothesis_name, type_is_prop_like, parse_top_level_binders, extract_decl_row, compute_hybrid_priority, resolve_decl_full_name, enrich_rows_with_graph, collect_rows, summarize, render_md, main`
- What it does: Defines DeclDebtRow, parse_args, normalize_target_path, load_targets, find_signature_end, find_top_level_colon

### `tools/infra/generate_keyword_research_report.py`

- Lines: `373`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, json, os, pathlib, re, subprocess`
- Classes: `CorpusFile`
- Top-level functions: `parse_args, git_head, list_tracked_lean_files, split_identifier, iter_corpus_files, build_term_index, top_files_by_mass, ensure_parent, render_markdown, main`
- What it does: Build a genuine full lexical index from all tracked Lean files.

### `tools/infra/generate_process_flow_report.py`

- Lines: `1259`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, time, typing`
- Top-level functions: `parse_args, load_jsonl, validate_schema, write_jsonl, write_json, edge_use_has_value, edge_use_has_type, compute_transport_credit, compute_defect_debt, classify_grade, feature_key, event_feature_out_bundles, build_event_target_index, is_duplicate_path_defect_row, max_witness_score, validate_exporter_contract, sequence_similarity, jaccard_distance`
- What it does: Defines parse_args, load_jsonl, validate_schema, write_jsonl, write_json

### `tools/infra/generate_projection_coloring.py`

- Lines: `538`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json, ordered_unique, parse_module_list, safe_float, short_name, md_table, stable_cluster_id, edge_mass, incidence_mass, add_affinity, classify_projection, main`
- What it does: Defines parse_args, load_json, ordered_unique, parse_module_list, safe_float

### `tools/infra/generate_replacement_frontier.py`

- Lines: `129`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, math, pathlib, sys, typing`
- Top-level functions: `calculate_replacement_priority, main`
- What it does: ⚖️ THE PAULI REPLACEMENT FRONTIER (Authority-Grounded)

### `tools/infra/generate_repo_story_from_keyword_index.py`

- Lines: `488`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, json, math, pathlib, re, subprocess`
- Classes: `DeclBlock`
- Top-level functions: `parse_args, git_head, load_json, list_tracked_lean_files, parse_decl_blocks, pick_characteristic_terms, deep_search_by_terms, infer_story_clusters, render_story, ensure_parent, main`
- What it does: Refactor full Lean keyword indexing into a declaration-grounded repo story.

### `tools/infra/generate_representation_depth_graph.py`

- Lines: `300`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, typing`
- Top-level functions: `parse_args, build_payload, render_md, main`
- What it does: Defines parse_args, build_payload, render_md, main

### `tools/infra/generate_semantic_flow_report.py`

- Lines: `725`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, math, pathlib, sys, typing`
- Top-level functions: `parse_args, load_jsonl, validate_schema, edge_use_has_value, edge_use_has_type, compute_transport_credit, compute_defect_debt, chirality_sign_from_polarity, stable_rate, build_index, diffusion_relaxation, kosaraju_scc, signed_component_frustration, markdown_table, main`
- What it does: Defines parse_args, load_jsonl, validate_schema, edge_use_has_value, edge_use_has_type

### `tools/infra/generate_semantic_quotient.py`

- Lines: `410`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json, parse_module_list, safe_float, build_surface_maps, theorem_shell_ratio, packet_contractibility, classify_residual, md_table, main`
- What it does: Defines parse_args, load_json, parse_module_list, safe_float, build_surface_maps

### `tools/infra/generate_sorry_equivalence.py`

- Lines: `162`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, sys, typing`
- Top-level functions: `generate_md, display_path, main`
- What it does: ⚖️ THE PAULI VACUITY STRATIFIER (Authority-Grounded)

### `tools/infra/generate_source_sink_compression.py`

- Lines: `1364`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, math, matplotlib, networkx, os, pathlib, re, sys`
- Top-level functions: `parse_args, short_name, load_native_structure, ordered_unique, build_native_lookup, native_component_corridor, summarize_native_decls, collapse_consecutive, motif_label, motif_signature, is_generated_decl_name, preferred_module_support_for_path, is_structure_field_projection, is_nested_local_theorem_surface, select_hotspot_modules, select_sink_rows, collect_source_stats, pick_canonical_source`
- What it does: Defines parse_args, short_name, load_native_structure, ordered_unique, build_native_lookup

### `tools/infra/generate_structural_dedup.py`

- Lines: `627`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json, ordered_unique, jaccard, parse_structure, component_repr, sort_component_ids, normalize_hydrated_rows, normalize_atomic_rows, normalize_sink_rows, parse_incidence, normalize_motif_signatures, short_name, role_rank, choose_canonical_sink, dedup_family_id, build_dedup_families, shadow_pair_features`
- What it does: Defines parse_args, load_json, ordered_unique, jaccard, parse_structure

### `tools/infra/generate_structural_dictionary.py`

- Lines: `435`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, pathlib, re, sys, typing`
- Top-level functions: `parse_args, load_json, load_jsonl, tokenize_name, stable_hash, bucket_degree, edge_kind_counts, top_items, module_family, initial_signature, wl_refine, render_md, main`
- What it does: Defines parse_args, load_json, load_jsonl, tokenize_name, stable_hash

### `tools/infra/generate_structural_fibers.py`

- Lines: `707`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json, ordered_unique, short_name, parse_structure, component_repr, component_reprs, normalize_atomic_rows, normalize_hydrated_rows, normalize_sink_rows, parse_incidence_edges, role_rank, choose_canonical_sink, common_prefix, common_suffix, branch_points, merge_points, jaccard`
- What it does: Defines parse_args, load_json, ordered_unique, short_name, parse_structure

### `tools/infra/generate_theorem_surface_index.py`

- Lines: `587`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, re, sys, typing`
- Classes: `DeclRow`
- Top-level functions: `parse_args, normalize_user_path, normalize_repo_relative, load_decl_rows, load_queue, load_quarantine_manifest, context_window, strongest_quarantine_bucket, match_audits, graph_profile_signal, stronger_confidence, classify_decl, render_md, main`
- What it does: Defines DeclRow, parse_args, normalize_user_path, normalize_repo_relative, load_decl_rows, load_queue

### `tools/infra/generate_theory_cloud_movie.py`

- Lines: `951`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, math, matplotlib, os, pathlib, random, subprocess, sys`
- Classes: `NodeInfo, Snapshot`
- Top-level functions: `parse_args, read_json, read_jsonl, git_show_text, read_json_from_commit, read_jsonl_from_commit, chirality_sign_from_polarity, compute_transport_credit, compute_defect_debt, build_decl_meta, build_topology_meta, build_rep_depth_map, build_semantic_fields, parse_edges, make_snapshot, seeded_rand01, initialize_positions, run_relaxation`
- What it does: Defines NodeInfo, Snapshot, parse_args, read_json, read_jsonl, git_show_text

### `tools/infra/generate_theory_spire_viz.py`

- Lines: `189`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, math, matplotlib, networkx, pathlib, sys, typing`
- Top-level functions: `run_aql, compute_layout, main`
- What it does: Generate a Spire-layered SVG visualization of the theory graph.

### `tools/infra/generate_truth_transport.py`

- Lines: `83`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, tools, typing`
- Top-level functions: `load_json, infer_run_id, build_from_run, parse_args, main`
- What it does: Generate an agent-to-agent truth transport packet from Hermes artifacts.

### `tools/infra/graph_hodge_spectrum.py`

- Lines: `708`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, numpy, pathlib, scipy, sys, time`
- Top-level functions: `load_graph, load_graph_from_arango, load_depth_tags, build_complex, graph_laplacian_sparse, directed_laplacian_sparse, fiedler_value, largest_eigenvalue, _cg_projected, kirchhoff_index_hutchinson, effective_resistance_samples, directed_asymmetry_score, build_chiral_signs, check_parity_mixing, sanity_check, main`
- What it does: Global spectral report on the undirected shadow of the declaration DAG.

### `tools/infra/gravitational_retrieval.py`

- Lines: `161`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, igf, json, pathlib, sys, tools`
- Classes: `ArangoTarget`
- Top-level functions: `_http_target, run_pregel_pagerank, get_lean_source, main`
- What it does: Defines ArangoTarget, _http_target, run_pregel_pagerank, get_lean_source, main

### `tools/infra/harvest_ground_truth.py`

- Lines: `102`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `json, os, pathlib, subprocess`
- Top-level functions: `harvest_file, main`
- What it does: Defines harvest_file, main

### `tools/infra/hash_signature.py`

- Lines: `22`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `hashlib, re, sys`
- Top-level functions: `normalize_ws, main`
- What it does: Defines normalize_ws, main

### `tools/infra/hermes_bounded_runner.py`

- Lines: `621`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, os, pathlib, re, subprocess, sys, textwrap, time`
- Classes: `Packet`
- Top-level functions: `utc_now, load_json, write_json, discover_packets, select_packet, packet_query, run_gravity_retrieval, summarize_gravity_context, build_prompt, call_openai_compatible, extract_text, parse_planner_route, build_truth_transport_packet, write_truth_transport, write_markdown, main`
- What it does: Run one bounded Hermes planning cycle over the research packet queue.

### `tools/infra/hermes_isolated_adapter.py`

- Lines: `261`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `hashlib, json, os, pathlib, shutil, subprocess, sys, yaml`
- Top-level functions: `run_checked, get_directory_hash, ensure_trace_index, setup_sandbox, check_backends, exec_subagent, load_task_manifest, main`
- What it does: Defines run_checked, get_directory_hash, ensure_trace_index, setup_sandbox, check_backends

### `tools/infra/hermes_leanstral_autoproof_loop.py`

- Lines: `353`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, hashlib, json, pathlib, re, sys, tools, typing`
- Classes: `ProofPrompt`
- Top-level functions: `_lean_feedback, error_signature, recommended_next_bee, build_autoproof_trace, make_local_leanstral_proposer, run_autoproof, parse_imports, _fake_proposer_from_candidates, build_arg_parser, main`
- What it does: Defines ProofPrompt, _lean_feedback, error_signature, recommended_next_bee, build_autoproof_trace, make_local_leanstral_proposer

### `tools/infra/hermes_vibe_coding_agent.py`

- Lines: `293`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, hashlib, json, os, pathlib, re, sys, typing, urllib`
- Classes: `LeanstralConfig`
- Top-level functions: `sha256_text, _strip_code_fence, sanitize_candidate, build_messages, openai_chat_transport, extract_assistant_content, propose, parse_imports, _load_text_arg, _fake_transport_from_file, build_arg_parser, main`
- What it does: Defines LeanstralConfig, sha256_text, _strip_code_fence, sanitize_candidate, build_messages, openai_chat_transport

### `tools/infra/hive_arango_queue.py`

- Lines: `2407`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, dataclasses, datetime, hashlib, json, os, pathlib, tools, typing, urllib`
- Classes: `CollectionSpec, IndexSpec`
- Top-level functions: `iso_now, iso_after, auth_header, request_json, sys_url, db_url, ensure_database, list_collections, ensure_collection, ensure_index, collection_count, aql, import_rows, stable_key, event_key, goal_key, fossil_key, task_key`
- What it does: MotherBee queue-oriented ArangoDB manifold bootstrap for Hive agents.

### `tools/infra/hive_audit_worker.py`

- Lines: `319`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, sys, time, tools, typing`
- Classes: `AuditBeeConfig`
- Top-level functions: `claim_audit_task, fetch_build_packet, fetch_verification_packet, fetch_upstream_provenance, infer_verification_origin, is_hard_audit_finding, audit_build, emit_audit_packet, run_one, parse_args, config_from_args, main`
- What it does: AuditBee worker for first-class Hive audit.semantic tasks.

### `tools/infra/hive_bee.py`

- Lines: `1563`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, os, pathlib, re, subprocess, sys, tempfile, time, tools`
- Classes: `BeeConfig, BeeAttempt`
- Top-level functions: `emit_packet, utc_now, sanitize_identifier, parse_imports, parse_context, build_gravity_query, build_leansearch_query, run_gravity_retrieval, run_leansearch_retrieval, run_leansearch_local_retrieval, run_retrieval, summarize_gravity_context, build_bee_prompt, extract_tactic, propose_tactic, infer_blocked_dependency, build_deadend_doc, build_fossil_record`
- What it does: Queue-backed autoproof bee for the live Hive manifold.

### `tools/infra/hive_bee_runner.py`

- Lines: `399`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, sys, time, typing`
- Classes: `RunnerError`
- Top-level functions: `utc_now, validate_envelope, role_policy, validate_task_policy, validate_result_contract, authority_lte, output_authority, load_input_packets, enforce_output_contract, build_result, run_task, write_json, cmd_run, parse_args, main`
- What it does: Bounded BeeTask runner over the local Hive packet store.

### `tools/infra/hive_build_worker.py`

- Lines: `280`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, os, pathlib, subprocess, sys, time, tools, typing`
- Classes: `BuildBeeConfig`
- Top-level functions: `emit_build_packet, claim_build_task, command_for_task, run_one, parse_args, config_from_args, main`
- What it does: BuildBee worker for first-class Hive build.verify tasks.

### `tools/infra/hive_leansearch_bee.py`

- Lines: `99`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, time`
- Top-level functions: `parse_args, config_from_args, main`
- What it does: LeanSearch-backed Hive proof bee lane.

### `tools/infra/hive_leanstral_bee_worker.py`

- Lines: `562`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, pathlib, sys, typing`
- Top-level functions: `utc_now, source_refs, extract_goal, extract_imports, ensure_task_is_bounded, packet_id_for, goal_hash, compact_excerpt, packet_envelope, embedded_trace_for, trace_ref_for, trace_attempts, build_repair_attempt_packet, build_autoproof_trace_packet, build_candidate_packet, build_residue_packet, build_output_packet, build_output_packets`
- What it does: Recurrent proposal-only Leanstral bee worker.

### `tools/infra/hive_local_packet_store.py`

- Lines: `322`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, shutil, sys, tempfile, typing`
- Classes: `StoreError`
- Top-level functions: `load_json, canonical_packet, canonical_json, packet_hash, validate_or_raise, read_store, write_store_atomic, append_packet, normalize_ref, refs_from, filter_records, emit_json, compact_record, records_by_id, cmd_append, cmd_list, cmd_show, cmd_parents`
- What it does: Append-only local JSONL store for schema-validated Hive packets.

### `tools/infra/hive_motherbee.py`

- Lines: `680`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, hashlib, json, pathlib, sys, typing`
- Classes: `MotherBeeError, RouteRule`
- Top-level functions: `stable_digest, record_id, task_key, task_id_for, task_created_at, packet_refs, record_references, has_unresolved_high_severity_pauli_block, trace_target_packet_id, trace_task_id, leanstral_attempt_indices, retry_count_for_hermes_leanstral, target_index, autoproof_frontier_repulsion, autoproof_frontier_instruction_suffix, latest_autoproof_trace_for_target, frontier_route_rule, enrich_task_from_autoproof_trace`
- What it does: Deterministic MotherBee scheduler v1 over the local Hive packet ledger.

### `tools/infra/hive_multichecker_merge.py`

- Lines: `382`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing`
- Top-level functions: `iter_jsonl, load_json_docs, first_string, nested_string, decl_of, module_of, kind_of, message_list, add_tool, load_declarations, leanparanoia_result, safeverify_result, autograder_problem_result, promotion_result, merge_reports, markdown_report, write_outputs, main`
- What it does: Merge Hive checker telemetry into one declaration-oriented report.

### `tools/infra/hive_packet_build.py`

- Lines: `1365`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, pathlib, re, sys, typing`
- Top-level functions: `utc_now, slug, stable_json, stable_digest, write_json, parse_ref_spec, uniq, base_envelope, with_metadata, require_non_empty, build_symbolic_seed, build_formulation_variant, build_resonance_cluster, build_pauli_critique, build_translation_control_packet, build_translation_packet, build_retrieval_hypothesis_packet, build_execution_intent_packet`
- What it does: Build Hive packets with repo-local defaults and optional schema validation.

### `tools/infra/hive_packet_path_runner.py`

- Lines: `554`
- AST status: `ok`
- CLI/entrypoint signals: `shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, tools, typing`
- Top-level functions: `_doc_key, _doc_ref, _lineage_edge, ingest_packet_chain_to_arango, utc_now, _ns, _ensure_valid, _route_fields, _seed_excerpt, emit_packet_chain`
- What it does: Emit one real Hive packet chain from a bounded Hermes planning cycle.

### `tools/infra/hive_packet_validate.py`

- Lines: `143`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, jsonschema, pathlib, sys, typing`
- Top-level functions: `load_json, build_store, choose_validator, format_error, validate_packet, cmd_validate, parse_args, main`
- What it does: Validate Hive packet JSON against repo-local machine-readable schemas.

### `tools/infra/hive_predigestion_ingest.py`

- Lines: `162`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `canonical_json, stable_hash, require_enum, iter_jsonl, validate_claim, make_task, build_tasks, write_jsonl, summary_for, main`
- What it does: Materialize Hive queue tasks from predigested claim packets.

### `tools/infra/hive_promotion_worker.py`

- Lines: `217`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, sys, time, tools, typing`
- Classes: `PromotionBeeConfig`
- Top-level functions: `claim_promotion_task, fetch_audit_packet, decide_promotion, emit_promotion_packet, run_one, parse_args, config_from_args, main`
- What it does: PromotionBee worker for explicit Hive promotion decisions.

### `tools/infra/hive_qi_heartbeat.py`

- Lines: `793`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, hashlib, json, os, pathlib, re, subprocess, typing`
- Classes: `Pulse`
- Top-level functions: `utc_now, sha, parse_heartbeat_log, parse_build_log_path, infer_declaration_name, parse_sorry_obligations_from_build_log, classify_blocker, parse_module_path, infer_geometric_sector, classify_geometric_sector, to_pulse_record, build_summary_record, load_identity_packets, load_identity_packets_from_run_dir, invoke_identity_runner, main`
- What it does: Convert heartbeat log pulses into Hive QI packets, lineage edges, and routed tasks.

### `tools/infra/hive_spec_submission_policy.py`

- Lines: `304`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, typing`
- Top-level functions: `stable_hash, iter_jsonl, unsound_marker_hits, declaration_names_from_source, make_target_spec_packet, make_submission_packet, validate_spec_submission_pair, load_json, load_audit_rows, promotion_gate, write_json, main`
- What it does: First-class Hive spec/submission lane for code-with-proof tasks.

### `tools/infra/hive_swarm.py`

- Lines: `438`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, sys, time, tools, typing`
- Classes: `SwarmConfig, CriticDecision, AuditorReport, SwarmRun`
- Top-level functions: `role_prompt, call_role_model, parse_keyed_line, parse_critic_decision, parse_auditor_report, write_artifact, audit_and_record, run_one, parse_args, config_from_args, main`
- What it does: Multi-role swarm worker for the live Hive queue.

### `tools/infra/hive_workflow_policy.py`

- Lines: `216`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, typing`
- Classes: `PolicyViolation`
- Top-level functions: `normalize_mode, declaration_header, changed_files, unsound_marker_hits, check_workflow_policy, load_files_map, write_report, main`
- What it does: Hive workflow policy checks inspired by Lean agent workflow packs.

### `tools/infra/hollow_semantic_auditor.py`

- Lines: `267`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, os, pathlib, re, sys, time, typing, urllib`
- Classes: `AuditResult, PauliAuditor`
- Top-level functions: `get_candidates, write_text_atomic, render_markdown, main`
- What it does: ⚖️ HOLLOW SEMANTIC AUDITOR

### `tools/infra/holonomy_auditor.py`

- Lines: `112`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, leantrail, pathlib, sys`
- Top-level functions: `_utc_now, run_holonomy_audit, _parse_args, main`
- What it does: Defines _utc_now, run_holonomy_audit, _parse_args, main

### `tools/infra/hydrate_arango_topology.py`

- Lines: `396`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, typing`
- Top-level functions: `read_jsonl, write_jsonl, node_key, edge_endpoint_key, collection_name, tarjan, hydrate, main`
- What it does: Hydrate raw Arango JSONL graph exports with topology labels.

### `tools/infra/hydrated_dag_to_lean_graph.py`

- Lines: `270`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, typing`
- Top-level functions: `load_structure, component_name, bfs_ids, select_ids, category_for, const_type_for, to_lean_graph_json, validate_rows, metadata_for, main`
- What it does: Project the hydrated SCC DAG into lean-graph's simple JSON schema.

### `tools/infra/hypothesis_fuser_and_lean_gate.py`

- Lines: `386`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, re, subprocess, typing`
- Top-level functions: `_utc_now, _stamp, _slug, _tokenize, _iter_jsonl, _read_goal, _extract_theorem_name, _preferred_target_name, _score_row, _compile_candidate, _write_skill, parse_args, main`
- What it does: Defines _utc_now, _stamp, _slug, _tokenize, _iter_jsonl

### `tools/infra/identity_protocol_metrics.py`

- Lines: `172`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, math, typing`
- Top-level functions: `_as_float, _pass, clamp01, jaccard_distance, extract_invariant_fingerprints, unresolved_fingerprint, compute_kappa_from_fingerprints, evaluate_gates, resolve_verdict, proxy_metrics_from_fixture, evaluate_identity_fixture`
- What it does: tools/infra/identity_protocol_metrics.py

### `tools/infra/identity_protocol_runner.py`

- Lines: `260`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, pathlib, sys, typing, uuid`
- Top-level functions: `utc_now_iso, sha256_json, load_json, load_jsonl, validate_fixture_expected_verdict, make_packet, write_packet, main`
- What it does: tools/infra/identity_protocol_runner.py

### `tools/infra/improver_trace_bridge.py`

- Lines: `304`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, csv, json, pathlib, typing`
- Top-level functions: `iter_input_paths, iter_records, as_bool, as_float, as_int, first_present, error_count, metric_direction, improvement_label, normalize_row, write_jsonl, summarize, run, main`
- What it does: Normalize ImProver proof-optimization traces into diagnostic telemetry.

### `tools/infra/ingest_chiral_sidecars.py`

- Lines: `231`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, requests, tools, typing`
- Top-level functions: `env, arango_ctx, req_json, ensure_collections, ensure_index, ensure_indexes, import_jsonl, fetch_name_to_id, resolve_members, verify_latest_summary, main`
- What it does: Ingest chiral sidecar JSONL artifacts into ArangoDB (immutable runs).

### `tools/infra/ingest_hive_json.py`

- Lines: `149`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, sys, typing`
- Classes: `HiveIngestError`
- Top-level functions: `parse_hive_lines, canonical_json_bytes, shape_for_packet, entity_key_for_packet, build_record, ingest_text, write_jsonl, write_manifest, read_input, parse_args, main`
- What it does: Extract, normalize, and persist HIVE_JSON packets emitted by HiveLogos.

### `tools/infra/ingest_semantic_content_audit.py`

- Lines: `495`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, pathlib, sys, typing`
- Top-level functions: `utc_stamp, stable_key, file_digest, read_json, iter_jsonl, write_jsonl, load_graph_index, module_decl_names, graph_context, source_excerpt_for_module, priority_for, status_allowed, enclosing_decl_name, enclosing_decl_object, finding_key_for, task_key_for, build_rows, import_rows_arango`
- What it does: Defines utc_stamp, stable_key, file_digest, read_json, iter_jsonl

### `tools/infra/injection_build_digest.py`

- Lines: `265`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, tools, typing`
- Top-level functions: `normalize_sources, format_sources_md, as_list, latest_history_time, main`
- What it does: Build a cited literature digest markdown from an injection packet.

### `tools/infra/injection_capture_gemini_cli.py`

- Lines: `361`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, subprocess, sys, time, tools, typing`
- Top-level functions: `sanitize_gemini_args, ensure_research, select_segments, build_prompt, run_gemini_cli, main`
- What it does: Capture Gemini CLI creative ideation into packet segment cards.

### `tools/infra/injection_chunk_ideate.py`

- Lines: `355`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, re, sys, tools, typing`
- Top-level functions: `ensure_research, normalize_text, split_sentences, split_oversized, syntactic_chunks, next_segment_index, parse_ideation_notes_file, write_prompt_files, main`
- What it does: Syntactically chunk packet intake text and seed per-segment ideation surfaces.

### `tools/infra/injection_common.py`

- Lines: `822`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, datetime, fcntl, hashlib, json, os, pathlib, platform, re, shutil, subprocess, sys`
- Classes: `PacketLockBusyError, PacketLock`
- Top-level functions: `utc_now, default_packet_id, status_for_lane, repo_root, injections_root, schema_path, resolve_packet, _parse_iso_datetime, _require_dict, _require_str, _require_str_list, _assert_no_extra_keys, _non_empty_str, validate_packet_schema, append_history_event, write_json_atomic, read_lock_metadata, packet_lock_path`
- What it does: Shared helpers for knowledge-injection packet tooling.

### `tools/infra/injection_create_packet.py`

- Lines: `103`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, os, pathlib, sys, tools`
- Top-level functions: `main`
- What it does: Create a new knowledge injection packet.

### `tools/infra/injection_enrich_segment.py`

- Lines: `210`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, sys, tools, typing`
- Top-level functions: `as_nonempty_list, ensure_research, find_or_create_segment, parse_evidence_rows, main`
- What it does: Update research workflow segments with creative notes and evidence.

### `tools/infra/injection_promote.py`

- Lines: `110`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, sys, tools`
- Top-level functions: `main`
- What it does: Promote injection claim packets between lifecycle lanes.

### `tools/infra/injection_research_packet.py`

- Lines: `183`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, os, pathlib, sys, tools`
- Top-level functions: `main`
- What it does: Seed a topic-focused deep-research packet in handover/injections.

### `tools/infra/injection_slo_report.py`

- Lines: `240`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, statistics, sys, tools, typing`
- Top-level functions: `parse_iso, pct, load_json_lines, packet_history_latency, main`
- What it does: Compute injection-pipeline SLO metrics and optional alert thresholds.

### `tools/infra/injection_status.py`

- Lines: `44`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib`
- Top-level functions: `main`
- What it does: Show lane counts for the knowledge injection subsystem.

### `tools/infra/jixia_batch_training.py`

- Lines: `301`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, subprocess, sys, tools, typing`
- Top-level functions: `_looks_like_lean_path, _path_from_packet_string, _collect_lean_paths_from_json, lean_files_from_cone_packets, discover_lean_files, raw_paths_for, normalized_dir_for, run_jixia_file, normalize_file, concat_jsonl, run_training_builder, run_pipeline, main`
- What it does: Run Jixia over Lean files and build local tactic-training data.

### `tools/infra/jixia_trace_bridge.py`

- Lines: `339`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `stable_hash, load_json_array, name_to_string, range_to_object, normalize_ppsyntax, normalize_goal, normalize_declaration, normalize_symbol, classify_info_node, iter_tactic_infos, normalize_tactic, normalize_line, write_jsonl, run_bridge, main`
- What it does: Normalize Jixia analyzer outputs into info-geometry JSONL sidecars.

### `tools/infra/lean_auto_trace_bridge.py`

- Lines: `291`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing`
- Top-level functions: `iter_input_paths, iter_records, as_list, as_bool, as_int, first_present, contains_trusted_sorry, normalize_solver, normalize_fact_inventory, normalize_translation, normalize_row, write_jsonl, summarize, run, main`
- What it does: Normalize lean-auto attempt traces into info-geometry diagnostic telemetry.

### `tools/infra/lean_autograder_report_bridge.py`

- Lines: `247`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, subprocess, typing`
- Top-level functions: `stable_hash, iter_json_docs, _first, coerce_problem_rows, normalize_problem, normalize_autograder_payload, write_outputs, normalize_existing_reports, run_autograder, main`
- What it does: Normalize lean4-autograder-style result reports into Hive telemetry.

### `tools/infra/lean_interact_wrapper.py`

- Lines: `227`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, dataclasses, json, os, pathlib, subprocess, sys, tempfile`
- Classes: `LeanProbe`
- Top-level functions: `_clean_lines, _build_source, run_lean_source, get_proof_state, apply_tactic, parse_imports, _usage, _pop_option, _pop_repeated, main`
- What it does: Defines LeanProbe, _clean_lines, _build_source, run_lean_source, get_proof_state, apply_tactic

### `tools/infra/leandojo_probe.py`

- Lines: `113`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, importlib, json, os, pathlib, platform, shutil, subprocess, sys`
- Top-level functions: `run, try_import, main`
- What it does: Defines run, try_import, main

### `tools/infra/leandojo_to_hermes_packets.py`

- Lines: `190`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, re, sys, tools`
- Top-level functions: `utc_now, slug, load_jsonl, build_packet, main`
- What it does: Defines utc_now, slug, load_jsonl, build_packet, main

### `tools/infra/leandojo_token_free.py`

- Lines: `133`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, importlib, json, pathlib, platform`
- Top-level functions: `try_import, load_sample_rows, main`
- What it does: Defines try_import, load_sample_rows, main

### `tools/infra/leandojo_v2_bridge.py`

- Lines: `420`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing`
- Top-level functions: `_pos, _pos_from_fields, _first, _tactics, _state_before, _state_after, _tactic_text, _dependency_name, _dependencies, convert_theorem_record, _iter_rows_from_payload, _iter_rows, _input_files, _decl_name_from_row, _decl_names_from_payload, load_decl_names, coverage_report, run_bridge`
- What it does: Phase A bridge: normalize LeanDojo-v2 traces into IG-compatible sidecars.

### `tools/infra/leanparanoia_audit_bridge.py`

- Lines: `230`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, subprocess, sys, typing`
- Top-level functions: `stable_hash, normalize_failure_map, finding_rows, normalize_paranoia_payload, parse_json_from_stdout, run_paranoia, iter_payloads, normalize_existing_reports, write_outputs, main`
- What it does: Normalize LeanParanoia proof-soundness audits into Hive telemetry.

### `tools/infra/leansearch_local.py`

- Lines: `258`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, math, pathlib, re, typing`
- Top-level functions: `tokenize, split_name_tokens, iter_jsonl, load_types, source_snippet, build_record, build_records, _idf, _score, search_records, main`
- What it does: Dependency-free LeanSearch-style retrieval over local DAG declaration artifacts.

### `tools/infra/lightcone_spectral_filter.py`

- Lines: `330`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, math, pathlib, sys, typing`
- Top-level functions: `require_numeric_stack, stable_node_name, _iter_nested_dicts, load_rows_and_edges, adjacency_matrix, matrix_norm, estimate_nilpotent_index, compute_drazin_from_schur, local_hodge_core, node_scores, finite_or_none, build_report, main`
- What it does: Local Schur/Drazin/Hodge diagnostics for bounded causal lightcones.

### `tools/infra/link_scorer_common.py`

- Lines: `344`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, dataclasses, hashlib, math, re, typing`
- Classes: `FeaturizerConfig`
- Top-level functions: `_hash_to_index_and_sign, _safe_text, _safe_float, _safe_bool, _normalize_identifier_token, _tokenize_identifier, _add_feature, _add_cat, _add_bool, _bucketize_log, _add_num, _add_tokens, row_to_sparse_features, sparse_dot, sigmoid, weighted_logloss, weighted_accuracy, binary_auc`
- What it does: Defines FeaturizerConfig, _hash_to_index_and_sign, _safe_text, _safe_float, _safe_bool, _normalize_identifier_token

### `tools/infra/llm_thermo_conformance.py`

- Lines: `550`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, math, pathlib, statistics, sys, typing`
- Classes: `CheckAccumulator`
- Top-level functions: `parse_args, load_jsonl, as_float, as_float_list, logsumexp, softmax_from_logits, close, pct, row_id, schema_validator, main`
- What it does: Numerical conformance checks for LLM thermo/operator identities.

### `tools/infra/logipedia_markdown_distill.py`

- Lines: `495`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, datetime, hashlib, json, pathlib, re, sys, typing`
- Top-level functions: `now_iso, stable_hash, slug, classify_claim, rank_for, risk_flags_for, extract_files, extract_decls, line_offsets, line_for_offset, candidate_chunks, packet_from_entry_fields, distill_markdown, path_exists, read_existing_path, audit_decision, owner_audit_from_entry, validate_or_die`
- What it does: Distill `docs/Logipedia.md`-style theorem-bank transcripts into Hive packets.

### `tools/infra/materialize_lossless_infotree.py`

- Lines: `490`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, hashlib, json, pathlib, typing`
- Classes: `RawEdge`
- Top-level functions: `read_jsonl, write_jsonl, stable_key, edge_key, module_of, endpoint_class, decl_attr_strings, representation_attrs, representation_labels, load_decl_map, load_raw_edges, load_lean_structural_topology, build, parse_args, main`
- What it does: Materialize a topology-preserving raw DAG graph for ArangoDB.

### `tools/infra/millennium_problem_bridge.py`

- Lines: `199`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, re, sys, tools, typing`
- Top-level functions: `line_of, extract_status_table, extract_declarations, problem_from_path, make_record, build_records, run_bridge, main`
- What it does: Build local retrieval records for LeanMillenniumPrizeProblems.

### `tools/infra/module_keyword_theory_program.py`

- Lines: `666`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, re, typing`
- Classes: `PathHit`
- Top-level functions: `rel, split_camel, decl_belongs_to_module, extract_keywords, iter_scan_files, count_keyword_in_text, repo_keyword_scan, load_jsonl, shortest_root_path, dependency_trace, candidate_decls_for_module, formulate_theorem_packet, collect_literature_context, parse_args, main`
- What it does: Defines PathHit, rel, split_camel, decl_belongs_to_module, extract_keywords, iter_scan_files

### `tools/infra/openai_deep_research_datasource_mcp_example.py`

- Lines: `97`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, json, pathlib, sys, typing`
- Top-level functions: `_json_text, search, fetch`
- What it does: Minimal search/fetch MCP datasource for OpenAI Deep Research.

### `tools/infra/openai_deep_research_gateway.py`

- Lines: `590`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, json, os, pathlib, sys, time, tools, typing`
- Top-level functions: `_asdict, _extract_output_text, _extract_status, _build_tools, _normalize_brief, _iter_dicts, _collect_evidence_rows, _ensure_research, _find_or_create_segment, _merge_text, _merge_evidence, _packet_ingest, dr_preflight_rewrite, dr_start, dr_status, dr_result, dr_run_blocking, dr_ingest_result_to_packet`
- What it does: Codex-facing MCP gateway for OpenAI Deep Research.

### `tools/infra/paperproof_bidirectional_cone.py`

- Lines: `300`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, typing`
- Top-level functions: `iter_jsonl, stable_hash, normalize, add_node, add_edge, decl_name_from_node, decl_file_from_node, component_key, cone_component_node, cone_decl_node, proof_node_id, load_cone_packet, build_cone_indexes, build_bidirectional_cone, write_jsonl, main`
- What it does: Join proof forests with Arango causal cone packets.

### `tools/infra/paperproof_jixia_compare.py`

- Lines: `261`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, hashlib, json, pathlib, re, typing`
- Top-level functions: `iter_jsonl, normalize_text, stable_hash, range_key, goal_pps_from_jixia, goal_pps_from_paperproof, source_key, step_signature, load_jixia_steps, load_paperproof_steps, multiset_overlap, compare_groups, build_report, render_markdown, main`
- What it does: Compare Paperproof-style proof packets with Jixia tactic transitions.

### `tools/infra/paperproof_proof_forest.py`

- Lines: `282`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, typing`
- Top-level functions: `iter_jsonl, stable_hash, normalize, tactic_family, goal_text, goal_raw_id, hyp_name, hyp_type, hyp_raw_id, add_node, add_edge, goal_node_id, hyp_node_id, build_forest, write_jsonl, main`
- What it does: Build proof-forest graphs from Paperproof-style trace packets.

### `tools/infra/paperproof_rpc_export_schema.py`

- Lines: `190`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `stable_hash, load_docs, proof_tree_from_doc, hyp_to_packet, goal_to_packet, hypotheses_from_goal, range_from_position, step_to_packet, packet_from_doc, write_jsonl, main`
- What it does: Normalize Paperproof RPC/webview proof trees into local trace packets.

### `tools/infra/paperproof_tableau_detector.py`

- Lines: `177`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, re, typing`
- Top-level functions: `iter_jsonl, normalize, family, goal_text, false_goal, contradiction_like_tactic, step_profile, profile_trace, write_jsonl, main`
- What it does: Detect semantic-tableau-like proof strategy in Paperproof traces.

### `tools/infra/paperproof_trace_bridge.py`

- Lines: `271`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, sys, typing`
- Top-level functions: `iter_jsonl, write_jsonl, goal_pp, hypothesis_from_context, hypotheses_from_goals, classify_trace_node, step_from_jixia, step_from_sft, group_key, packet_for_group, build_packets, render_markdown, main`
- What it does: Render proof-state telemetry as Paperproof-style proof-history packets.

### `tools/infra/paperproof_training_effects.py`

- Lines: `147`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, re, typing`
- Top-level functions: `iter_jsonl, stable_hash, family, normalize_goal_count, effect_labels, rows_from_packet, write_jsonl, main`
- What it does: Label tactic effects from Paperproof-style proof-history packets.

### `tools/infra/pauli_authority_bridge.py`

- Lines: `194`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, base64, collections, dataclasses, json, math, os, pathlib, subprocess, sys, tools, typing`
- Classes: `PauliProfile`
- Top-level functions: `_arango_auth_header, _repo_context_allows_live_authority, run_cmd, ensure_truth_artifacts, _jsonl_line_count, get_authority_data`
- What it does: ⚖️ THE PAULI AUTHORITY BRIDGE

### `tools/infra/pda_forml4_bridge.py`

- Lines: `233`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `stable_hash, first, as_text, process_label, iter_json_records, normalize_record, _split_from_path, run_bridge, main`
- What it does: Normalize PDA/FormL4-style autoformalization records into IG sidecars.

### `tools/infra/plot_decl_graph.py`

- Lines: `435`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, math, matplotlib, networkx, os, pathlib, sys, typing`
- Top-level functions: `parse_args, plot_module_graph, write_hotspot_json, render_burndown_markdown, write_burndown_reports, write_summary, main`
- What it does: Defines parse_args, plot_module_graph, write_hotspot_json, render_burndown_markdown, write_burndown_reports

### `tools/infra/prima_materia_ingest.py`

- Lines: `126`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, os, requests, sys, typing`
- Classes: `Arango`
- Top-level functions: `now_iso, env, load_json, main`
- What it does: Phase-1 Prima Materia ingest (ArangoDB).

### `tools/infra/real_prover_trace_bridge.py`

- Lines: `249`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `stable_hash, iter_json_records, normalize_state, normalize_node, normalize_call, normalize_collect_result, normalize_real_record, run_bridge, main`
- What it does: Normalize REAL-Prover traces into info-geometry training telemetry.

### `tools/infra/refresh_blueprint_tags.py`

- Lines: `420`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, re, sys, typing`
- Top-level functions: `parse_args, normalize_user_path, load_decl_rows, is_generated_or_unstable_name, prefix_match, module_to_path, collect_import_closure, read_file_lines, locate_source_decl, source_decl_is_blueprint_addressable, collect_explicit_blueprints, render_auto_blueprints, render_blueprint_facade, main`
- What it does: Defines parse_args, normalize_user_path, load_decl_rows, is_generated_or_unstable_name, prefix_match

### `tools/infra/refresh_decl_graph.py`

- Lines: `209`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, subprocess, sys`
- Top-level functions: `parse_args, main`
- What it does: Defines parse_args, main

### `tools/infra/report_rep_layers.py`

- Lines: `82`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, typing`
- Top-level functions: `read_jsonl, layer_of, report, parse_args, main`
- What it does: Report L0-L5 representation-layer counts and cross-layer raw edges.

### `tools/infra/reports/__init__.py`

- Lines: `0`
- AST status: `ok`
- What it does: Empty package marker.

### `tools/infra/reports/classify_markdown_corpus.py`

- Lines: `427`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, re, subprocess, sys, typing`
- Top-level functions: `parse_args, tracked_files, untracked_files, is_markdown, command_line_count, heading_count, fenced_code_count, tokenize, add_score, classify_markdown, render_markdown, main`
- What it does: Defines parse_args, tracked_files, untracked_files, is_markdown, command_line_count

### `tools/infra/reports/common.py`

- Lines: `45`
- AST status: `ok`
- Imports: `__future__, datetime, json, pathlib, sys, typing`
- Top-level functions: `normalize_user_path, load_json, read_text, write_text, relpath, generated_timestamp`
- What it does: Defines normalize_user_path, load_json, read_text, write_text, relpath

### `tools/infra/reports/generate_bilingual_spine_report.py`

- Lines: `479`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, sys, typing`
- Classes: `ModuleAudit`
- Top-level functions: `parse_args, module_to_path, parse_imports, extract_module_docstring, declaration_docstring_gaps, build_import_closure, audit_module, build_markdown_report, build_json_payload, sanitize_module_filename, build_stub_text, write_stub_bundle, main`
- What it does: Defines ModuleAudit, parse_args, module_to_path, parse_imports, extract_module_docstring, declaration_docstring_gaps

### `tools/infra/reports/generate_bridge_candidates.py`

- Lines: `280`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, re, sys`
- Top-level functions: `parse_args, safe_slug, decl_tail, infer_transport_shape, risk_from_row, display_source_file, signature_sketch, candidate_name, render_packet, main`
- What it does: Defines parse_args, safe_slug, decl_tail, infer_transport_shape, risk_from_row

### `tools/infra/reports/generate_bridge_thinness_index.py`

- Lines: `147`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, dataclasses, datetime, pathlib, re, sys`
- Classes: `Finding`
- Top-level functions: `priority_for, is_target, trim_proof, classify_block, collect_findings, render_md, main`
- What it does: Defines Finding, priority_for, is_target, trim_proof, classify_block, collect_findings

### `tools/infra/reports/generate_debt_candidates.py`

- Lines: `406`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, pathlib, re, sys`
- Classes: `DebtSignal, DebtTarget`
- Top-level functions: `parse_args, file_bucket, normalize_name, parse_queue, aggregate_targets, strongest_priority, risk_for_target, sort_targets, slugify, locate_decl_start, extract_signature, nearby_declarations, category_hint, render_packet, main`
- What it does: Defines DebtSignal, DebtTarget, parse_args, file_bucket, normalize_name, parse_queue

### `tools/infra/reports/generate_llm_debt_prompts.py`

- Lines: `202`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys`
- Top-level functions: `parse_args, render_creative, render_critical, main`
- What it does: Defines parse_args, render_creative, render_critical, main

### `tools/infra/reports/generate_llm_frontier_prompts.py`

- Lines: `188`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys`
- Top-level functions: `parse_args, render_creative, render_critical, main`
- What it does: Defines parse_args, render_creative, render_critical, main

### `tools/infra/reports/generate_markdown_hygiene_report.py`

- Lines: `430`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, re, subprocess, sys, time, typing`
- Top-level functions: `parse_args, load_json, to_rel, normalize_title, iter_markdown_links, resolve_link_target, git_last_commit_unix, classify_action, build_markdown, main`
- What it does: Defines parse_args, load_json, to_rel, normalize_title, iter_markdown_links

### `tools/infra/reports/generate_repository_surface_index.py`

- Lines: `269`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, subprocess, sys`
- Top-level functions: `parse_args, tracked_files, untracked_files, is_config_path, top_level_bucket, extension_bucket, render_markdown, main`
- What it does: Defines parse_args, tracked_files, untracked_files, is_config_path, top_level_bucket

### `tools/infra/reports/generate_self_optimization_report.py`

- Lines: `99`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__`
- Top-level functions: `frontier_names, render_report, main`
- What it does: Defines frontier_names, render_report, main

### `tools/infra/reports/generate_surrogate_index.py`

- Lines: `455`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, json, pathlib, re, subprocess, sys`
- Classes: `Decl, Finding`
- Top-level functions: `module_to_relpath, is_comment_line, file_bucket, priority_for, find_decl_at_or_before, collect_constructivity_findings, dedupe_findings, collect_findings, run_surrogate_gate, summarize_counts, top_queue, render_md, parse_args, main`
- What it does: Defines Decl, Finding, module_to_relpath, is_comment_line, file_bucket, priority_for

### `tools/infra/reports/generate_unification_index.py`

- Lines: `412`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, pathlib, sys`
- Classes: `ModuleEntry, UnificationEntry`
- Top-level functions: `parse_args, status_explainer, render_md, main`
- What it does: Defines ModuleEntry, UnificationEntry, parse_args, status_explainer, render_md, main

### `tools/infra/reports/generate_vacuity_index.py`

- Lines: `109`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, pathlib, re, sys`
- Classes: `Finding`
- Top-level functions: `parse_args, active_priority, collect_findings, render_md, main`
- What it does: Defines Finding, parse_args, active_priority, collect_findings, render_md, main

### `tools/infra/representation_depth_from_graph.py`

- Lines: `262`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, typing`
- Top-level functions: `read_jsonl, as_int, node_name, node_depth_nat, node_depth_slug, node_is_capstone, edge_src_dst, sorted_unique, lower_depths, nearest_lower_depth, shallowest_lower_depth, reaches_prev, reaches_below_prev, reaches_above, judgment_label, closure_from, build_report, report_from_dir`
- What it does: Derive representation-depth rows from materialized graph artifacts.

### `tools/infra/representation_depth_io.py`

- Lines: `197`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, collections, json, pathlib, tools, typing`
- Top-level functions: `load_json, rel_repo_path, interval_label, load_depth_index, module_to_rel_file, inferred_file_kind, load_lean_tags, merge_depth_files, build_depth_sources`
- What it does: Defines load_json, rel_repo_path, interval_label, load_depth_index, module_to_rel_file

### `tools/infra/rerank_arango_links.py`

- Lines: `588`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, dataclasses, datetime, hashlib, json, leantrail, numpy, pathlib, sys, tools`
- Classes: `ArangoTarget`
- Top-level functions: `_utc_now, _safe_text, _safe_int, _iter_jsonl, _load_model, _snapshot_from_path, _auth_header, _db_url, _request_json, _aql, _fetch_arango_neighborhood, _read_file_snippet, _decl_kind_of, _to_decl_payload, _is_declaration_node, _node_name, _stable_id, _build_candidates`
- What it does: Defines ArangoTarget, _utc_now, _safe_text, _safe_int, _iter_jsonl, _load_model

### `tools/infra/research_controller.py`

- Lines: `581`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, pathlib, re, subprocess, sys, typing`
- Classes: `CommandResult, Metrics, Verdict, Iteration`
- Top-level functions: `utc_now, slugify, run_cmd, load_json, file_age_hours, coerce_count, needs_refresh, read_keyword_metrics, read_deep_search_metrics, read_significance_metrics, collect_metrics, evaluate, select_subtask, build_actions, write_state, parse_args, main`
- What it does: Closed-loop repo research controller.

### `tools/infra/research_digest_worker.py`

- Lines: `197`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, os, pathlib, re, subprocess, sys, time, tools, typing`
- Top-level functions: `parse_args, sanitize, shell, extract_ids, build_run_dir, import_event, process_task, run_once, main`
- What it does: Defines parse_args, sanitize, shell, extract_ids, build_run_dir

### `tools/infra/research_packet.py`

- Lines: `336`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, re, sys, typing`
- Top-level functions: `utc_now, confidence_bucket, slug, load_json, write_json, _uniq, build_packet_from_state, validate_packet, cmd_build, cmd_validate, parse_args, main`
- What it does: Research packet builder + validator.

### `tools/infra/residue_quarantine.py`

- Lines: `85`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `datetime, json, jsonschema, pathlib, sys`
- Top-level functions: `absorb_failure, main`
- What it does: Defines absorb_failure, main

### `tools/infra/rethlas_verification_bridge.py`

- Lines: `169`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `stable_hash, iter_json_docs, _findings, validate_rethlas_payload, normalize_rethlas_payload, run_bridge, main`
- What it does: Normalize Rethlas verification reports into local audit telemetry.

### `tools/infra/run_copilot_codex_lean_pipeline.py`

- Lines: `170`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, sys, tools, typing`
- Top-level functions: `utc_now, build_codex_prompt, build_pipeline_payload, write_json, run_pipeline, parse_args, main`
- What it does: Defines utc_now, build_codex_prompt, build_pipeline_payload, write_json, run_pipeline

### `tools/infra/run_full_dag_toolchain.py`

- Lines: `251`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, os, pathlib, subprocess, sys`
- Top-level functions: `run_step, process_exists, preflight_build_lock_health, main`
- What it does: Defines run_step, process_exists, preflight_build_lock_health, main

### `tools/infra/run_locked_lake_build.py`

- Lines: `45`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys`
- Top-level functions: `parse_args, main`
- What it does: Defines parse_args, main

### `tools/infra/run_predigestion_to_hive_demo.py`

- Lines: `161`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, tools, typing`
- Top-level functions: `write_json, read_jsonl, sample_rows, run_demo, main`
- What it does: Run a reproducible predigestion-to-Hive dry run.

### `tools/infra/run_proof_prompt_batch.py`

- Lines: `258`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, subprocess, sys, tools, typing`
- Top-level functions: `utc_now, backend_defaults, extract_completion_text, assess_output_quality, build_result_payload, write_json, write_markdown, run_openai_prompt, run_copilot_prompt, run_prompt, parse_args, main`
- What it does: Defines utc_now, backend_defaults, extract_completion_text, assess_output_quality, build_result_payload

### `tools/infra/run_socratic_alchemy_batch.py`

- Lines: `70`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, subprocess, sys`
- Top-level functions: `parse_args, main`
- What it does: Batch runner for Socratic alchemy loops over multiple seed prompt files.

### `tools/infra/run_socratic_alchemy_loop.py`

- Lines: `1029`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, re, subprocess, sys, tools`
- Top-level functions: `run, write, read, strip_code_fences, compile_lean, module_name_from_file, extract_compiled_decl_names, extract_first_theorem_surface, _referenced_identifiers, _sanitize_where_block, _extract_named_decl_blocks, strip_lean_comments, extract_probe_context, normalize_probe_goal, normalize_probe_tactic, probe_goal, probe_tactic, check_gemini_guard`
- What it does: Run a guarded Gemini -> Codex -> guarded Gemini Socratic alchemy loop.

### `tools/infra/safeverify_audit_bridge.py`

- Lines: `257`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, subprocess, typing`
- Top-level functions: `stable_hash, iter_json_docs, const_kind, axioms_of, normalize_safeverify_outcome, write_outputs, normalize_existing_reports, run_safeverify, main`
- What it does: Normalize SafeVerify target/submission verification into Hive telemetry.

### `tools/infra/scan_third_party_licenses.py`

- Lines: `292`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, json, os, pathlib, re, subprocess`
- Classes: `Hit, FileFinding`
- Top-level functions: `run, load_owner_names, load_excluded_prefixes, is_text_file, iter_files, classify, scan_file, write_markdown, main`
- What it does: Defines Hit, FileFinding, run, load_owner_names, load_excluded_prefixes, is_text_file

### `tools/infra/score_link_candidates.py`

- Lines: `123`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, numpy, pathlib, sys, tools, typing`
- Top-level functions: `_iter_jsonl, _load_model, parse_args, main`
- What it does: Defines _iter_jsonl, _load_model, parse_args, main

### `tools/infra/select_openclaw_target.py`

- Lines: `335`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json_file, seed_for_row, slugify, make_structural_commands, make_uncovered_debt_commands, normalize_uncovered_debt_rows, normalize_structural_rows, build_payload, render_primary, render_markdown, main`
- What it does: Defines parse_args, load_json_file, seed_for_row, slugify, make_structural_commands

### `tools/infra/semantic_audit.py`

- Lines: `228`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, hashlib, json, pathlib, re, subprocess, sys`
- Top-level functions: `normalize_ws, sha256_text, extract_decl_signature, get_current_imports, get_repo_root, get_git_file, import_delta_ok, check_forbidden_constructs, validate_task_schema, main`
- What it does: Defines normalize_ws, sha256_text, extract_decl_signature, get_current_imports, get_repo_root

### `tools/infra/shadow_plant_worker.py`

- Lines: `407`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, pathlib, sys, tools, typing`
- Top-level functions: `canonical_json, stable_key, read_json, require_safe_consensus, extract_consensus_items, ensure_shadow_collections, build_rows, write_report, main`
- What it does: Epistemic Reactor: gated shadow planting worker.

### `tools/infra/socratic_packet_to_sampler_jsonl.py`

- Lines: `135`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, typing`
- Top-level functions: `parse_args, _target_source, _target_priority, _canonical_target_key, _select_targets, main`
- What it does: Convert a Socratic packet into sampler-style JSONL rows for hypothesis_fuser_and_lean_gate.

### `tools/infra/timings.py`

- Lines: `176`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, datetime, json, pathlib, re, typing`
- Top-level functions: `indexer_timing_log_path, indexer_timing_json_path, report_timing_json_path, parse_indexer_timing_log, build_indexer_timing_payload, write_indexer_timing_sidecar, load_indexer_timing, write_report_timing_sidecar, load_report_timing, format_elapsed_ms, top_timing_rows, timing_matches_meta`
- What it does: Defines indexer_timing_log_path, indexer_timing_json_path, report_timing_json_path, parse_indexer_timing_log, build_indexer_timing_payload

### `tools/infra/trace_and_retrieve.py`

- Lines: `104`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `json, os, pathlib, re, subprocess, sys`
- Top-level functions: `get_git_sha, get_cache_path, build_index, retrieve, main`
- What it does: Defines get_git_sha, get_cache_path, build_index, retrieve, main

### `tools/infra/train_link_scorer.py`

- Lines: `297`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, math, numpy, pathlib, random, sys, tools, typing`
- Classes: `Example`
- Top-level functions: `_iter_jsonl, _to_examples, _predict_probs, _eval_split, parse_args, main`
- What it does: Defines Example, _iter_jsonl, _to_examples, _predict_probs, _eval_split, parse_args

### `tools/infra/ulam_trace_bridge.py`

- Lines: `158`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, hashlib, json, pathlib, typing`
- Top-level functions: `stable_hash, as_text, iter_json_records, normalize_record, run_bridge, main`
- What it does: Normalize UlamAI run.jsonl traces into info-geometry tactic telemetry.

### `tools/infra/validate_raw_infotree_export.py`

- Lines: `486`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, typing`
- Top-level functions: `read_jsonl, validate, parse_args, main`
- What it does: Validate the stage-1 raw InfoTree export contract.

### `tools/infra/verify_layered_arango_descent.py`

- Lines: `166`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, igf, json, pathlib, sys, tools, typing`
- Top-level functions: `aql, main`
- What it does: Verify raw-to-overlay-to-raw descent in the layered Arango graph.

### `tools/infra/verify_raw_infotree_arango_descent.py`

- Lines: `517`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, arango_raw_infotree_ingest, argparse, dataclasses, json, pathlib, sys, tools, typing`
- Classes: `QueryCheck`
- Top-level functions: `run_aql, load_json, structural_checks, count_report, leakage_report, tactic_report, run_checks, parse_args, main`
- What it does: Verify raw_infotree_* descent invariants in ArangoDB.

### `tools/infra/visualize_causal_chiral_cone_packet.py`

- Lines: `342`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, html, json, pathlib, typing`
- Top-level functions: `_component_key, _component_label, _short, _overlay_component_keys, _collect_nodes, _layout, _render_svg, _render_summary, render_html, main`
- What it does: Render a causal/chiral cone prompt packet as a small offline HTML view.

### `tools/lean4-skills/analyze_let_usage.py`

- Lines: `372`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `dataclasses, pathlib, re, sys, typing`
- Classes: `LetBinding`
- Top-level functions: `count_tokens, find_let_bindings, count_binding_uses, analyze_binding, analyze_file, format_output, analyze_specific_binding, main`
- What it does: Analyze let binding usage to detect false-positive optimization candidates.

### `tools/lean4-skills/find_exact_candidates.py`

- Lines: `262`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `dataclasses, pathlib, re, sys, typing`
- Classes: `ProofBlock`
- Top-level functions: `find_proof_end, get_tactic_lines, classify_proof, find_candidates, main`
- What it does: Find proof blocks that are good candidates for `exact?` replacement.

### `tools/lean4-skills/find_golfable.py`

- Lines: `699`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `dataclasses, pathlib, re, sys, typing`
- Classes: `GolfablePattern`
- Top-level functions: `count_lines_in_range, count_binding_uses, find_let_have_exact, find_by_exact, find_calc_chains, find_constructor_branches, find_multiple_haves, find_have_calc, find_apply_exact_chains, _sort_key, analyze_file, analyze_files, format_output, main`
- What it does: Find proof-golfing opportunities in Lean 4 files.

### `tools/lean4-skills/minimize_imports.py`

- Lines: `259`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `pathlib, re, shutil, subprocess, sys, typing`
- Top-level functions: `extract_imports, remove_import_line, check_compiles, minimize_imports, main`
- What it does: minimize_imports.py - Remove unused imports from Lean 4 files

### `tools/lean4-skills/parse_command_args.py`

- Lines: `92`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `command_args, json, os, sys`
- Top-level functions: `main`
- What it does: Standalone CLI for the lean4 slash-command parser.

### `tools/lean4-skills/parse_lean_errors.py`

- Lines: `221`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `hashlib, json, pathlib, re, sys, typing`
- Top-level functions: `parse_location, classify_error, extract_goal, extract_local_context, extract_code_snippet, extract_suggestion_keywords, compute_error_hash, parse_lean_errors, _build_error_dict, main`
- What it does: Parse Lean compiler errors into structured JSON for repair routing.

### `tools/lean4-skills/solver_cascade.py`

- Lines: `153`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `json, pathlib, subprocess, sys, tempfile, typing`
- Top-level functions: `try_solver, run_solver_cascade, main`
- What it does: Try automated solvers in sequence before resampling with LLM.

### `tools/lean4-skills/sorry_analyzer.py`

- Lines: `490`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `dataclasses, json, pathlib, re, subprocess, sys, typing`
- Classes: `Sorry`
- Top-level functions: `strip_lean_comments_and_strings, extract_declaration_name, extract_documentation, find_sorries_in_file, find_sorries, format_text, format_markdown, format_json, format_summary, interactive_mode, show_file_sorries, show_sorry_details, main`
- What it does: sorry_analyzer.py - Extract and analyze sorry statements in Lean 4 code

### `tools/lean4-skills/test_apply_exact_chains.py`

- Lines: `97`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `find_golfable, pathlib, sys, tempfile`
- Top-level functions: `main`
- What it does: Fixture tests for find_apply_exact_chains() in find_golfable.py.

### `tools/lean4-skills/try_exact_at_step.py`

- Lines: `370`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `os, pathlib, re, shutil, subprocess, sys, typing`
- Top-level functions: `find_project_root, find_proof_bounds, replace_proof_with_exact_q, run_lean_and_capture, test_exact_at, main`
- What it does: Try `exact?` at various points in Lean 4 proofs to find one-liner replacements.

### `tools/lean_improver_probe.py`

- Lines: `201`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, typing`
- Classes: `ProofCandidate`
- Top-level functions: `leading_spaces, decl_name, count_tactics, hints_for, theorem_blocks, iter_lean_files, render_prompt, main`
- What it does: ImProver-style proof optimization probe for local Lean modules.

### `tools/leantrail/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: LeanTrail tooling package.

### `tools/leantrail/adapters.py`

- Lines: `530`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, csv, hashlib, json, leantrail, pathlib, typing, xml`
- Top-level functions: `load_snapshot, save_snapshot, _json_text, _parse_json_text, _iter_jsonl, _stable_key, export_graphml, import_graphml, export_neo4j_csv, import_neo4j_csv, export_arango_json, import_arango_json`
- What it does: Defines load_snapshot, save_snapshot, _json_text, _parse_json_text, _iter_jsonl

### `tools/leantrail/arango_ingest.py`

- Lines: `151`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, igf, json, pathlib, sys, tools`
- Classes: `ArangoTarget`
- Top-level functions: `_ensure_collections, _read_text, _http_target, _import_jsonl, _collection_count, _parse_args, main`
- What it does: Defines ArangoTarget, _ensure_collections, _read_text, _http_target, _import_jsonl, _collection_count

### `tools/leantrail/arango_physics_evaluator.py`

- Lines: `549`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, base64, dataclasses, datetime, json, leantrail, pathlib, sys, tools, typing, urllib`
- Classes: `PhysicsWeights, ArangoTarget`
- Top-level functions: `_utc_now, _safe_float, _snapshot_from_path, _local_eval, _auth_header, _db_url, _request_json, _aql, _arango_eval, _compute_metrics, _render_md, _parse_args, main`
- What it does: Defines PhysicsWeights, ArangoTarget, _utc_now, _safe_float, _snapshot_from_path, _local_eval

### `tools/leantrail/conformance.py`

- Lines: `696`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, json, leantrail, pathlib, sys, tools, typing`
- Classes: `PathQuery`
- Top-level functions: `_utc_now, _read_snapshot, _jaccard, _pct_drift, _top_ids, _edge_key, _compute_scc_signature, _default_path_queries, _load_path_queries, _load_required_locked_paths, _render_md, run_conformance, _parse_args, main`
- What it does: Defines PathQuery, _utc_now, _read_snapshot, _jaccard, _pct_drift, _top_ids

### `tools/leantrail/export.py`

- Lines: `86`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, sys, tools`
- Top-level functions: `_parse_args, main`
- What it does: Defines _parse_args, main

### `tools/leantrail/failure_harvester.py`

- Lines: `471`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, pathlib, re, typing`
- Top-level functions: `_utc_now, _utc_iso, _iter_jsonl, _norm_file, _load_decl_index, _closest_decl, _classify_error_kind, _extract_decl_mentions, _load_edge_kind_index, _failure_id, _record_from_existing, _merge_failure, run_failure_harvest, _parse_args, main`
- What it does: Defines _utc_now, _utc_iso, _iter_jsonl, _norm_file, _load_decl_index

### `tools/leantrail/hole_packets.py`

- Lines: `477`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, datetime, hashlib, json, leantrail, pathlib, sys, tools, typing`
- Classes: `HoleAccumulator`
- Top-level functions: `_utc_now, _iter_jsonl, _stable_hole_id, _load_required_lock_status, _build_holes, _annotate_paths, _annotate_required_locks, _render_md, run_hole_packets, _parse_args, main`
- What it does: Defines HoleAccumulator, _utc_now, _iter_jsonl, _stable_hole_id, _load_required_lock_status, _build_holes

### `tools/leantrail/path_lock_registry.py`

- Lines: `236`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, hashlib, json, leantrail, pathlib, sys, tools, typing`
- Top-level functions: `_utc_now, _snapshot_from_path, _path_id, _load_registry, _row_fingerprint, _write_registry, run_registry_update, _parse_args, main`
- What it does: Defines _utc_now, _snapshot_from_path, _path_id, _load_registry, _row_fingerprint

### `tools/list_collections.py`

- Lines: `27`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, tools`
- Top-level functions: `default_target, main`
- What it does: Defines default_target, main

### `tools/pathing.py`

- Lines: `131`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, pathlib`
- Top-level functions: `repo_root, lean_root, resolve_existing, default_src_root, default_docs_map_root, default_artifacts_root, default_decl_artifact_root, default_decl_graph_file, default_decl_index_dir, default_decl_meta_file, default_decl_metadata_file, default_source_sink_bipartite_file, default_decl_structure_file, default_build_decl_artifact_root, default_build_decl_graph_file, default_build_decl_index_dir, default_build_decl_metadata_file, resolve_decl_graph_file`
- What it does: Defines repo_root, lean_root, resolve_existing, default_src_root, default_docs_map_root

### `tools/planner/__init__.py`

- Lines: `1`
- AST status: `ok`
- What it does: Planner package for vacuity matching, normalization, ranking, and reporting.

### `tools/planner/admissibility.py`

- Lines: `293`
- AST status: `ok`
- Imports: `__future__, common, policy, typing`
- Top-level functions: `_admissibility_overlap, _evaluate_replacement_precheck, rank_admissibility_prechecks`
- What it does: Strict admissibility precheck scaffold logic.

### `tools/planner/common.py`

- Lines: `467`
- AST status: `ok`
- Imports: `__future__, collections, dataclasses, json, pathlib, typing, urllib`
- Classes: `Signal, RankedEntry`
- Top-level functions: `clamp01, safe_mean, relpath_or_self, parse_uri_or_path, coerce_int, arity_shape, binder_shape, is_valid_decl_name, normalize_expr_record, make_cluster_key, dedup_preserve_order, top_counts, keys_from_counts, first_count_key, top_count_keys, jaccard_overlap, load_json, load_jsonl`
- What it does: Shared planner types, constants, and helpers.

### `tools/planner/matching.py`

- Lines: `576`
- AST status: `ok`
- Imports: `__future__, bisect, collections, common, pathlib, typing`
- Top-level functions: `_iter_decl_container_nodes, _find_decl_context_value, extract_decl_field, extract_location_hints, _new_decl_match_context, _index_decl_match_context_entry, _finalize_decl_match_context, build_decl_match_context_from_decls, build_decl_match_context, _unique_decl, _line_candidates, _resolve_nearest_decl_from_ordered, _resolve_decl_by_location, _payload_cluster_keys, _resolve_decl_by_fingerprint, resolve_decl_match, seed_decl_match_context`
- What it does: Planner matching context and declaration resolution logic.

### `tools/planner/normalization.py`

- Lines: `574`
- AST status: `ok`
- Imports: `__future__, collections, common, json, matching, pathlib, tools, typing`
- Top-level functions: `collect_bridge_json_paths, extract_bridge_payload_objects, observe_bridge_payload, normalize_bridge_observations`
- What it does: Bridge observation normalization and signal extraction.

### `tools/planner/policy.py`

- Lines: `47`
- AST status: `ok`
- Imports: `__future__`
- Top-level functions: `cluster_rank_weight, precheck_status_priority, planner_policy_snapshot`
- What it does: Planner policy constants and calibration helpers.

### `tools/planner/ranking.py`

- Lines: `812`
- AST status: `ok`
- Imports: `__future__, collections, common, policy, tools, typing`
- Top-level functions: `rank_vacuity_candidates, rank_owner_candidates, rank_declaration_plans, rank_fingerprint_corridors, rank_replacement_candidates`
- What it does: Ranking logic for vacuity, owner, replacement, corridor, and declaration plans.

### `tools/planner/report.py`

- Lines: `187`
- AST status: `ok`
- Imports: `__future__, common, json, policy, typing`
- Top-level functions: `make_markdown_report`
- What it does: Markdown and JSON report rendering for vacuity planner outputs.

### `tools/plot_decl_graph.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/proof_driver.py`

- Lines: `157`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, re, typing`
- Top-level functions: `parse_args, load_json, placeholder_reasons, selected_sketch, insert_before_namespace_end, materialize_signature, write_report, main`
- What it does: Defines parse_args, load_json, placeholder_reasons, selected_sketch, insert_before_namespace_end

### `tools/quality/__init__.py`

- Lines: `0`
- AST status: `ok`
- What it does: Empty package marker.

### `tools/quality/audit_constructivity.py`

- Lines: `395`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, sys`
- Classes: `Finding`
- Top-level functions: `rel, module_to_path, read_quarantine_manifest, quarantined_paths, iter_files, line_of, strip_comments, scan_manifest_consistency, scan_file, print_findings, main`
- What it does: Defines Finding, rel, module_to_path, read_quarantine_manifest, quarantined_paths, iter_files

### `tools/quality/audit_docstrings.py`

- Lines: `88`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, pathlib, re, sys`
- Top-level functions: `audit_file, run_audit`
- What it does: Defines audit_file, run_audit

### `tools/quality/audit_naming.py`

- Lines: `100`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, pathlib, re, sys`
- Top-level functions: `is_snake_case, is_upper_camel_case, is_lower_camel_case, audit_file, run_audit`
- What it does: Defines is_snake_case, is_upper_camel_case, is_lower_camel_case, audit_file, run_audit

### `tools/quality/audit_semantic.py`

- Lines: `733`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, re, subprocess, sys, typing`
- Classes: `InterfaceInfo`
- Top-level functions: `rel, module_to_path, line_of, path_to_module, strip_lean_comments, declaration_modules, read_quarantine_manifest, quarantined_paths, iter_files, read_files, make_finding, scan_banned_constructs, scan_constant_collapse, is_proof_like_type, parse_interfaces, scan_raw_witness_bundles, scan_ghost_classes, count_name_occurrences`
- What it does: Defines InterfaceInfo, rel, module_to_path, line_of, path_to_module, strip_lean_comments

### `tools/quality/audit_style.py`

- Lines: `85`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, pathlib, re, sys`
- Top-level functions: `audit_file, run_audit`
- What it does: Defines audit_file, run_audit

### `tools/quality/check_closure_debt_gate.py`

- Lines: `142`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, re, sys, typing`
- Top-level functions: `parse_args, load_json, tokenize_count, collect_group_modules, main`
- What it does: Defines parse_args, load_json, tokenize_count, collect_group_modules, main

### `tools/quality/check_equivalence_dictionary_gate.py`

- Lines: `131`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, json, pathlib, sys, typing`
- Top-level functions: `parse_args, load_json, compute_report_metrics, main`
- What it does: Defines parse_args, load_json, compute_report_metrics, main

### `tools/quality/check_frontier_integrity_gate.py`

- Lines: `221`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, sys, typing`
- Classes: `PatternRule, Finding`
- Top-level functions: `parse_args, load_config, parse_rules, iter_cluster_files, unique_build_targets, line_for_offset, scan_files, main`
- What it does: Hard integrity gate for closure/spectral/sinkhorn frontier clusters.

### `tools/quality/check_translation_registry.py`

- Lines: `127`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, pathlib, re, sys`
- Top-level functions: `parse_args, read_registry_rows, anchor_in_registry, anchor_declared, main`
- What it does: Defines parse_args, read_registry_rows, anchor_in_registry, anchor_declared, main

### `tools/quality/closure_ast_validator.py`

- Lines: `46`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, json, pathlib, sys`
- Top-level functions: `validate_ast, main`
- What it does: Closure AST Validator: Ensures only allowed Lean AST node types are present in closure modules.

### `tools/quality/closure_debt_auditor.py`

- Lines: `198`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, collections, json, math, os, pathlib, re, tools`
- Top-level functions: `parse_lean_decls, get_arango_edges, find_theory_islands, main`
- What it does: Closure Debt Auditor: Identifies unanchored Lean declarations, theory islands, and holes in the dependency graph.

### `tools/quality/common.py`

- Lines: `43`
- AST status: `ok`
- Imports: `__future__, pathlib, sys`
- Top-level functions: `resolve_target_dir, iter_lean_files, print_grouped_violations`
- What it does: Defines resolve_target_dir, iter_lean_files, print_grouped_violations

### `tools/quality/detect_hollow_theorems.py`

- Lines: `50`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `pathlib, re, sys`
- Top-level functions: `is_hollow_proof, scan_lean_file, main`
- What it does: Hollow Theorem Detector for Lean Codebases

### `tools/quality/detect_ornamental_hypotheses.py`

- Lines: `42`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `pathlib, re, sys`
- Top-level functions: `scan_lean_file, main`
- What it does: Ornamental Hypothesis Detector for Lean Codebases

### `tools/quality/dvorak_audit.py`

- Lines: `61`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `argparse, json, pathlib, re`
- Top-level functions: `audit_file, main`
- What it does: Defines audit_file, main

### `tools/quality/functorial_invariance_audit.py`

- Lines: `402`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, sys, typing`
- Classes: `Corridor`
- Top-level functions: `rel, load_jsonl, has_rep_depth, parse_args, load_rep_tagged_names, shortest_path_to_canopy, main`
- What it does: Defines Corridor, rel, load_jsonl, has_rep_depth, parse_args, load_rep_tagged_names

### `tools/quality/kanban_evidence_lint.py`

- Lines: `582`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, sys, typing`
- Classes: `Finding`
- Top-level functions: `rel, load_json_or_jsonl, normalize_payload, nonempty, produced, value_at, has_any, has_any_list, normalize_state, task_id, authority_level, has_context_evidence, has_patch_evidence, has_build_evidence, has_audit_evidence, has_promotion_evidence, has_blocker_evidence, has_quarantine_evidence`
- What it does: Defines Finding, rel, load_json_or_jsonl, normalize_payload, nonempty, produced

### `tools/quality/mathfulness_audit.py`

- Lines: `414`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, json, pathlib, re, typing`
- Top-level functions: `load_json, load_jsonl, rel, repo_path, source_block, significance_by_name, policy_lint_flags, paranoia_flags, classify, main`
- What it does: Unified mathfulness audit for info-geometry-lean declarations.

### `tools/quality/pauli_seal_audit.py`

- Lines: `667`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, json, pathlib, re, sys, typing`
- Classes: `Finding`
- Top-level functions: `rel, strip_comments, count_density, line_of, declaration_header, has_shared_param_keyword, scan_file, load_json, main`
- What it does: Defines Finding, rel, strip_comments, count_density, line_of, declaration_header

### `tools/quality/semantic_content_audit.py`

- Lines: `736`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, collections, dataclasses, json, pathlib, re, sys, typing`
- Classes: `ModuleAudit`
- Top-level functions: `rel, module_name, module_to_path, read_manifest, in_scope, all_infogeometry_files, importers_by_module, importer_class, importer_class_counts, forbidden_importers_for_status, resolve_finding_location, finding_in_scope, source_excerpt, declaration_headers, enclosing_decl, finding_payload, semantic_status, collect_findings`
- What it does: Defines ModuleAudit, rel, module_name, module_to_path, read_manifest, in_scope

### `tools/query_arango.py`

- Lines: `36`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, base64, json, os, urllib`
- Top-level functions: `query, main`
- What it does: Defines query, main

### `tools/query_dag.py`

- Lines: `37`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, base64, json, os, urllib`
- Top-level functions: `query, main`
- What it does: Defines query, main

### `tools/refactor_namespaces.py`

- Lines: `122`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, os`
- Top-level functions: `refactor_file, main`
- What it does: Defines refactor_file, main

### `tools/refresh_blueprint_tags.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/refresh_decl_graph.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/run_arango_query.py`

- Lines: `23`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, tools`
- Top-level functions: `default_target, main`
- What it does: Defines default_target, main

### `tools/run_arango_query2.py`

- Lines: `29`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `__future__, tools`
- Top-level functions: `default_target, main`
- What it does: Defines default_target, main

### `tools/run_locked_lake_build.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/run_optimization_cycle.py`

- Lines: `1401`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, dataclasses, datetime, json, os, pathlib, re, shlex, subprocess, sys, typing`
- Classes: `CommandResult, CandidateSketch, HydrationResult, ProofAttemptRecord`
- Top-level functions: `acquire_worktree_lock, release_worktree_lock, hydrate_symlink, hydrate_worktree_from_local_lake, now_utc_compact, run_capture, run_text, branch_exists, ensure_clean_tracked_tree, load_json, load_text, parse_args, selected_frontier_rows, _capture_section, _capture_inline_value_optional, _capture_code_block_optional, _capture_section_optional, _normalize_sketch_block`
- What it does: Defines CommandResult, CandidateSketch, HydrationResult, acquire_worktree_lock, release_worktree_lock, hydrate_symlink

### `tools/select_openclaw_target.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/semantic_block_export.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/skynet_v2.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/theorem_significance.py`

- Lines: `544`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang`
- Imports: `__future__, collections, dataclasses, json, os, pathlib, sys, typing`
- Classes: `DeclInfo, ProofShape, GraphSignals, BridgeEvidence, ScoreEntry`
- Top-level functions: `build_proof_shape, _is_generated, _is_role_exempt, _in_strict_path, _is_bridge_file, _is_certified_surface, _uncertified_twin_name, _reachable, _longest_reverse_depth, _scc_sizes, _graph_signals, _vacuity_score, score_all, _count_bridge_evidence, _payload_file, _repo_relative_file, load_bridge_evidence_index, main`
- What it does: ⚖️ THE PAULI SIGNIFICANCE AUDITOR (Authority-Grounded)

### `tools/update_repo_docs.py`

- Lines: `10`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard`
- Imports: `pathlib, sys, tools`
- What it does: Script/module with top-level Python statements; inspect before operational use.

### `tools/vacuity_planner.py`

- Lines: `409`
- AST status: `ok`
- CLI/entrypoint signals: `__main__ guard, shebang, argparse`
- Imports: `__future__, argparse, datetime, json, pathlib, sys, tools, typing`
- Top-level functions: `parse_args, _load_graph_from_arango, _load_graph_inputs, main`
- What it does: Planning-only vacuity planner orchestrator.

### `tools/vacuity_policy_config.py`

- Lines: `71`
- AST status: `ok`
- CLI/entrypoint signals: `shebang`
- Imports: `__future__, pathlib`
- Top-level functions: `is_bridge_file, is_strict_file, expected_violation_level`
- What it does: Shared vacuity policy configuration for Layer B and Layer C.
