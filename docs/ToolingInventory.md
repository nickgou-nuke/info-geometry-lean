# Tooling Inventory

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Inventory of active tool surfaces, package lanes, Lean DAG tooling, and shell orchestration.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/ToolingMethodology.md](ToolingMethodology.md), [tools/README.md](../tools/README.md)

This file inventories the executable tooling surface of the repository.

It is intentionally scoped to tool-bearing code:

- Python package and CLI surfaces
- Lake-managed scripts
- `lean/DAG/` and related Lean tooling
- Python tools under `tools/`
- compatibility and utility scripts under `scripts/`
- shell orchestration scripts

It does not try to inventory theorem modules under `lean/InfoGeometry/` or test files under `tests/` unless they are directly part of the toolchain contract.

## Snapshot

Current tool counts from the checked-in repo:

- `src/igf/`: 27 Python files
- `cli/`: 2 Python files
- `tools/`: 288 Python files, 28 shell scripts
- `scripts/`: 19 Python files, 19 shell scripts
- `lean/DAG/`: 48 Lean modules, 1 Python ingestion helper
- `lean/scripts/DAG/Exploration/`: 15 Lean exploration modules

## Trust Order

When tool surfaces disagree, use this order:

1. Lean source and kernel-checked declarations
2. Lake entrypoints in [lakefile.lean](../lakefile.lean)
3. Maintained package/API surfaces under `src/igf/`
4. Maintained tool directories under `tools/infra/`, `tools/frontier/`, `tools/leantrail/`, `tools/quality/`, `tools/docs/`
5. Compatibility wrappers under top-level `tools/*.py`, `cli/`, and `scripts/`

## Entrypoints

### Installed Python CLIs

From [pyproject.toml](../pyproject.toml):

- `igf`
  Canonical package CLI backed by [src/igf/cli.py](../src/igf/cli.py).
- `infogeometry`
  Compatibility CLI backed by [scripts/cli.py](../scripts/cli.py).

### Lake-managed Scripts

From [lakefile.lean](../lakefile.lean):

- `strictCheck`
  Runs `scripts/quality/strict-check.sh`.
- `semanticAudit`
  Runs `tools/quality/audit_semantic.py`.
- `semanticSnapshot`
  Runs `tools/frontier/semantic_snapshot.py`.
- `proofSession`
  Runs `tools/frontier/proof_session.py`.
- `proofPrint`
  Runs `tools/frontier/proof_print.py`.
- `graphToBlueprint`
  Archived compatibility wrapper over `archive/legacy/scripts/graph_to_blueprint_inplace.py`.
- `refreshBlueprintTags`
  Runs `tools/infra/refresh_blueprint_tags.py`.
- `bilingualSpineReport`
  Runs `tools/infra/reports/generate_bilingual_spine_report.py`.
- `dagStatus`
  Runs `tools/infra/dag_status.py`.
- `dagRefresh`
  Runs `tools/infra/dag_refresh.py`.
- `dagReports`
  Runs `tools/infra/dag_reports.py`.
- `dagDoctor`
  Runs `tools/infra/dag_doctor.py`.
- `dagAll`
  Runs `tools/infra/dag_all.py`.
- `changedVerify`
  Runs `tools/infra/changed_verify.py`.
- `leantrailConformance`
  Runs `tools/leantrail/conformance.py`.
- `leantrailExport`
  Runs `tools/leantrail/export.py`.
- `leantrailArangoIngest`
  Runs `tools/leantrail/arango_ingest.py`.
- `leantrailArangoPhysicsEval`
  Runs `tools/leantrail/arango_physics_evaluator.py`.
- `leantrailFailureHarvest`
  Runs `tools/leantrail/failure_harvester.py`.
- `leantrailPathLock`
  Runs `tools/leantrail/path_lock_registry.py`.
- `leantrailHolePackets`
  Runs `tools/leantrail/hole_packets.py`.

## Package Surface

### `src/igf/`

This is the greenfield Python package surface. It is the cleanest part of the migration and already owns a real vertical slice of the artifact pipeline.

#### CLI

- [src/igf/cli.py](../src/igf/cli.py)
  Canonical package entrypoint. Supports `preflight`, `build`, `run`, `validate`, `normalize`, `ingest`, `verify`, `maxent-candidates`, `barrier-candidates`, and `report`.

#### Config

- [src/igf/config/env_aliases.py](../src/igf/config/env_aliases.py)
  Environment-variable alias resolution.
- [src/igf/config/loader.py](../src/igf/config/loader.py)
  Loads package/runtime config, especially Arango-facing config.
- [src/igf/config/model.py](../src/igf/config/model.py)
  Typed config model definitions.
- [src/igf/config/preflight.py](../src/igf/config/preflight.py)
  Preflight checks and machine-readable readiness reporting.

#### Artifacts

- [src/igf/artifacts/io.py](../src/igf/artifacts/io.py)
  Artifact reading and writing helpers.
- [src/igf/artifacts/manifest.py](../src/igf/artifacts/manifest.py)
  Manifest generation and normalization support.
- [src/igf/artifacts/compatibility_adapters.py](../src/igf/artifacts/compatibility_adapters.py)
  Bridges old artifact shapes into the new package contract.

#### Graph / Arango

- [src/igf/graph/arango_client.py](../src/igf/graph/arango_client.py)
  Arango connection helper.
- [src/igf/graph/collections.py](../src/igf/graph/collections.py)
  Collection names and collection contract helpers.
- [src/igf/graph/indexes.py](../src/igf/graph/indexes.py)
  Index setup and index expectations.
- [src/igf/graph/query_registry.py](../src/igf/graph/query_registry.py)
  Canonical AQL query registry for package-owned queries.
- [src/igf/graph/query_runner.py](../src/igf/graph/query_runner.py)
  Query execution helpers.

#### Pipeline

- [src/igf/pipeline/build.py](../src/igf/pipeline/build.py)
  Builds patch artifacts from LeanTrail/graph exports.
- [src/igf/pipeline/validate.py](../src/igf/pipeline/validate.py)
  Schema and artifact validation.
- [src/igf/pipeline/ingest.py](../src/igf/pipeline/ingest.py)
  Arango ingestion of package-owned artifacts.
- [src/igf/pipeline/verify.py](../src/igf/pipeline/verify.py)
  Verification queries against ingested runs.
- [src/igf/pipeline/candidates.py](../src/igf/pipeline/candidates.py)
  Candidate ranking for maxent/log-barrier style patch suggestions.
- [src/igf/pipeline/report.py](../src/igf/pipeline/report.py)
  Package-owned artifact reporting.
- [src/igf/pipeline/orchestrator.py](../src/igf/pipeline/orchestrator.py)
  Offline end-to-end package pipeline orchestration.

#### Policy

- [src/igf/policy/claim_scope.py](../src/igf/policy/claim_scope.py)
  Claim/authority scope typing for artifact surfaces.

### CLI Compatibility Wrappers

- [cli/igf.py](../cli/igf.py)
  Thin wrapper that imports and runs `igf.cli.main`.
- [tools/igf.py](../tools/igf.py)
  Same role as `cli/igf.py`, retained for compatibility.
- [tools/ig.py](../tools/ig.py)
  Older “IG Spire Orchestrator” CLI; partially overlaps with the package build lane and should be treated as legacy-adjacent.

## Lean Tooling Surface

### `lean/DAG/`

This is the Lean-native graph export and structural analysis layer. It is the authoritative source for declaration-graph extraction and graph-side structural invariants.

#### Core graph construction

- `Basic.lean`, `Hydrate.lean`, `Topo.lean`, `Dominators.lean`, `SCC.lean`, `Util.lean`
  Graph types, graph extraction from the environment, SCC condensation, topological order, dominators, and shared utilities.

#### Analysis

- `Analysis.lean`, `Impact.lean`, `Betti.lean`, `TwoComplex.lean`, `GraphHodge.lean`
  Reachability, influence, vulnerability, homology-style summaries, two-complex structure, and spectral/Hodge analysis.

#### Export

- `Indexer.lean`, `ExportDecls.lean`, `ExportForwardGraph.lean`, `StructuralExport.lean`, `SkeletonExport.lean`, `RepresentationDepthExport.lean`, `RootOrderExport.lean`, `HolonomyExporter.lean`, `ProcessFlowExport.lean`, `ExprArangoExport.lean`, `BlockExport.lean`, `ServerExport.lean`, `RawInfoTreeExport.lean`
  Emit the JSON/JSONL surfaces consumed by the Python layers.

#### Search and query

- `SearchCore.lean`, `Search.lean`, `SearchRank.lean`, `FinalSearch.lean`, `SearchByHash.lean`, `QueryEngine.lean`, `SemanticServerRpc.lean`
  Name search, token ranking, batch search, hash search, structured query evaluation, and semantic RPC.

#### Algebraic / categorical extensions

- `CategoryBridge.lean`, `Functor.lean`, `ExactMorphism.lean`, `Isomorphism.lean`, `LiftNaturality.lean`, `KernelExtract.lean`, `SubgraphMatch.lean`, `FindFinrank.lean`
  Morphism detection, categorical lifts, exactness, isomorphism tracking, and subgraph/correspondence structure.

#### Extraction / disassembly

- `Disassembler.lean`, `GlobalDisassembler.lean`, `ExprFingerprint.lean`, `GroundTruthHarvester.lean`
  Expr-level decomposition, repo-wide disassembly, expression fingerprints, and harvested structural truth surfaces.

#### Tests and integration

- `CategoryBridgeTest.lean`, `ExactMorphismTest.lean`, `SearchCoreTests.lean`, `IntegrationTest.lean`
  Lean-side DAG test modules.

#### Support files

- [lean/DAG/ingest.py](../lean/DAG/ingest.py)
  Python-side helper for consuming Lean DAG exports.
- [lean/DAG/README.md](../lean/DAG/README.md)
  Maintained inventory and conceptual explanation of the DAG layer.
- `decl_edges.jsonl`, `decls.jsonl`
  Checked-in sample/export-side data artifacts.

### `lean/scripts/DAG/Exploration/`

These are exploration or server-facing Lean tools rather than the main authoritative export lane.

- `Betti.lean`, `Disassembler.lean`, `FinalSearch.lean`, `Isomorphism.lean`, `QueryEngine.lean`, `Search.lean`, `SearchRank.lean`
  Interactive/standalone exploration variants of DAG analyses.
- `CompilerBridgeServer.lean`, `SemanticBlockServer.lean`, `SemanticSnapshotServer.lean`
  Server-style or bridge-style exploration frontends.
- `SemanticBlockExport.lean`
  Semantic block export exploration surface.
- `NaturalityDiagnostics.lean`, `NaturalityPromoter.lean`, `SquarePromoter.lean`
  Structure-promotion and naturality diagnostics.
- `Common.lean`
  Shared exploration helpers.

## Python Tools by Directory

### `tools/infra/`

This is the largest operational lane. It contains the managed DAG corridor, audits, Arango/LeanTrail ingestion, report generation, research packet handling, and agentic orchestration.

#### DAG and build orchestration

- `dag_status.py`, `dag_refresh.py`, `dag_reports.py`, `dag_doctor.py`, `dag_all.py`
  Managed operator path for DAG refresh, reports, diagnostics, and end-to-end runs.
- `build.py`, `artifacts.py`, `dag_config.py`, `dag_manifest.py`
  Shared config/artifact plumbing for the DAG lane.
- `refresh_decl_graph.py`, `refresh_blueprint_tags.py`
  Refresh the declaration graph and blueprint tag surfaces.
- `run_locked_lake_build.py`, `build_changed_lean.py`, `changed_verify.py`, `run_full_dag_toolchain.py`
  Controlled Lean build, changed-file verification, and full toolchain runs.
- `timings.py`
  Timing-sidecar helpers.

#### Graph, Arango, and audit surfaces

- `decl_graph.py`, `decl_graph_support.py`, `plot_decl_graph.py`
  Graph loading, support utilities, and visualization.
- `arango_env.py`, `arango_dag_algorithms.py`, `arango_gravity_context.py`, `arango_fidelity_audit.py`, `arango_layered_ingest.py`, `arango_raw_infotree_graph.py`, `arango_raw_infotree_ingest.py`, `arango_structural_vacuity_audit.py`
  Arango configuration, graph algorithms, ingestion, and audit surfaces.
- `hydrate_arango_topology.py`, `materialize_lossless_infotree.py`, `validate_raw_infotree_export.py`, `verify_layered_arango_descent.py`, `verify_raw_infotree_arango_descent.py`
  Expr/info-tree hydration and fidelity verification.
- `extract_expr_fingerprints.py`, `hash_signature.py`
  Structural signatures and expression fingerprints.

#### Report and index generation

- `generate_causal_report.py`, `generate_process_flow_report.py`, `generate_source_sink_compression.py`
  Causal-flow and source/sink reporting.
- `generate_structural_dedup.py`, `generate_structural_dictionary.py`, `generate_structural_fibers.py`, `generate_semantic_quotient.py`, `generate_projection_coloring.py`
  Structural compression and clustering reports.
- `generate_representation_depth_graph.py`, `representation_depth_from_graph.py`, `representation_depth_io.py`, `report_rep_layers.py`
  Representation-depth analysis and report surfaces.
- `generate_equivalence_dictionary.py`, `generate_theorem_surface_index.py`, `generate_hypothesis_debt_report.py`, `generate_replacement_frontier.py`
  Surface indexing and theorem/hypothesis debt ranking.
- `generate_keyword_research_report.py`, `generate_repo_story_from_keyword_index.py`, `module_keyword_theory_program.py`
  Repo-wide lexical indexing and story synthesis.
- `generate_black_books_keyword_report.py`, `generate_black_books_story_from_keyword_index.py`
  Black Books lexical indexing and story synthesis.
- `generate_theory_cloud_movie.py`, `generate_theory_spire_viz.py`, `generate_truth_transport.py`
  Visual or synthesized high-level report surfaces.

#### Policy, lint, and obstruction diagnostics

- `canonical_policy_lint.py`, `agentic_policy_lint.py`
  Repo policy and protocol linting.
- `check_bipartite_bleed.py`, `check_gauge_obstruction_tags.py`, `check_hollow_theorems.py`, `check_representation_depth.py`, `check_research_handoff_gate.py`, `check_semantic_flow_report.py`
  Focused policy/audit gates.
- `find_vacuous.py`, `hollow_semantic_auditor.py`, `holonomy_auditor.py`, `pauli_authority_bridge.py`
  Vacuity, hollow-surface, holonomy, and Pauli-facing audit tools.
- `apex_defect_profile.py`, `causal_cone_spectrum.py`, `graph_hodge_spectrum.py`, `debug_gravity.py`
  Local obstruction and structural diagnostics.

#### Hypothesis and candidate generation

- `candidate_bridge_packet.py`, `build_claim_packet.py`, `claim_promote.py`
  Build and promote candidate or claim packets.
- `build_link_ats_dataset.py`, `train_link_scorer.py`, `score_link_candidates.py`, `rerank_arango_links.py`
  Link-prediction and reranking lane.
- `dual_hypothesis_sampler.py`, `hypothesis_fuser_and_lean_gate.py`, `select_openclaw_target.py`
  Candidate hypothesis generation, fusion, and Lean gating.

#### Research and injection pipeline

- `research_packet.py`, `research_controller.py`, `research_digest_worker.py`
  Typed research packet creation and iterative research control.
- `injection_common.py`, `injection_create_packet.py`, `injection_research_packet.py`, `injection_chunk_ideate.py`, `injection_enrich_segment.py`, `injection_build_digest.py`, `injection_promote.py`, `injection_status.py`, `injection_slo_report.py`
  Hermes/injection packet workflow from intake to promotion.
- `injection_capture_gemini_cli.py`, `gemini_account_adapter.py`, `gemini_cli_guard.py`
  Gemini-facing capture and guarded execution helpers.
- `openai_deep_research_gateway.py`, `openai_deep_research_datasource_mcp_example.py`
  OpenAI deep-research adapter examples/gateway support.
- `trace_and_retrieve.py`, `gravitational_retrieval.py`
  Retrieval helpers over repo structure and graph context.

#### Generative / alchemical lane

- `alchemical_loop.py`, `run_socratic_alchemy_loop.py`, `run_socratic_alchemy_batch.py`
  Socratic/Jung/Pauli style generative discovery loops.
- `prima_materia_ingest.py`
  Prima-materia intake and conversion helper.
- `run_proof_prompt_batch.py`, `run_copilot_codex_lean_pipeline.py`
  Prompt-batch and agentic proof-execution helpers.

#### Hive / swarm / worker lane

- `hive_arango_queue.py`, `hive_audit_worker.py`, `hive_bee.py`, `hive_build_worker.py`, `hive_leansearch_bee.py`, `hive_packet_build.py`, `hive_packet_path_runner.py`, `hive_packet_validate.py`, `hive_promotion_worker.py`, `hive_qi_heartbeat.py`, `hive_swarm.py`
  Hive queue, worker, packet, and swarm orchestration.
- `hermes_bounded_runner.py`, `hermes_isolated_adapter.py`
  Hermes bounded or isolated execution adapters.
- `identity_protocol_runner.py`, `identity_protocol_metrics.py`
  Identity protocol runtime and metrics.

#### Lean interaction and external adapters

- `lean_interact_wrapper.py`, `leandojo_probe.py`, `leandojo_to_hermes_packets.py`, `leandojo_token_free.py`
  Lean or LeanDojo interaction helpers.
- `compiler_bridge_client.py` lives under `tools/frontier/`, but this lane consumes its artifacts.

#### Release / export / compliance

- `export_public_release.py`, `scan_third_party_licenses.py`
  Public-release export and license scanning.
- `residue_quarantine.py`
  Quarantine/residue management.

### `tools/frontier/`

This is the targeted proof/semantic inspection lane.

- `semantic_snapshot.py`
  Semantic snapshot export for specific Lean surfaces.
- `semantic_block_export.py`
  Block-level semantic export helper.
- `proof_session.py`, `proof_runtime.py`, `proof_print.py`
  Proof-state and declaration inspection helpers.
- `compiler_bridge_client.py`
  Client for compiler-bridge style semantic services.
- `extract_module_patch.py`
  Module-scoped patch extraction for frontier workflows.
- `skynet_v2.py`
  Frontier automation / proof-support runner.

### `tools/leantrail/`

This is the graph-query and carrier-conformance lane.

- `conformance.py`
  Carrier/snapshot conformance checking.
- `export.py`
  LeanTrail snapshot/export builder.
- `arango_ingest.py`
  Ingests LeanTrail/Expr export surfaces into Arango.
- `arango_physics_evaluator.py`
  Derived physics-style evaluation over Arango-ingested LeanTrail data.
- `failure_harvester.py`
  Harvests failures into LeanTrail memory surfaces.
- `path_lock_registry.py`
  Maintains path-lock records.
- `hole_packets.py`
  Builds or tracks hole packets.
- `adapters.py`
  Shared adapters for the LeanTrail lane.

### `tools/quality/`

This is the focused lint/audit lane.

- `audit_constructivity.py`, `audit_docstrings.py`, `audit_naming.py`, `audit_semantic.py`, `audit_style.py`
  Repository quality and semantic audits.
- `check_closure_debt_gate.py`, `check_equivalence_dictionary_gate.py`, `check_frontier_integrity_gate.py`, `check_translation_registry.py`
  CI-style gates and registry checks.
- `closure_ast_validator.py`, `closure_debt_auditor.py`
  Closure-debt analysis and AST validation.
- `detect_hollow_theorems.py`, `detect_ornamental_hypotheses.py`
  Hollow theorem and ornamental hypothesis detection.
- `dvorak_audit.py`, `functorial_invariance_audit.py`, `pauli_seal_audit.py`
  Specialized audits aligned with repo doctrine.
- `common.py`
  Shared helpers.

### `tools/docs/`

This is the documentation maintenance lane.

- `generate_auto_docs.py`
  Auto-generate documentation artifacts.
- `refresh_markdown_status.py`
  Assigns and refreshes status blocks across the Markdown corpus.
- `update_repo_docs.py`
  Repo-doc refresh/update helper.

### `tools/alexandria/`

This is the literature/retrieval and context-ingestion lane.

- `fetch_arxiv_corpus.py`
  Fetches literature corpora.
- `semantic_ingest.py`, `arango_ingest.py`
  Ingestion into local semantic/Arango stores.
- `retrieve_context.py`, `graph_context_rank.py`
  Context retrieval and ranking.
- `repair_lineage.py`
  Repairs lineage/provenance structures.
- `render_socratic_dossier.py`
  Produces a Socratic dossier artifact.
- `structural_chunking.py`, `alexandria_algorithms.py`, `schema.py`
  Chunking, ranking, and schema support.

### `tools/planner/`

Planning/ranking support for candidate generation:

- `admissibility.py`
  Admissibility logic.
- `matching.py`
  Matching and candidate pairing.
- `normalization.py`
  Normalization helpers.
- `policy.py`
  Planner policy.
- `ranking.py`
  Candidate ranking.
- `report.py`
  Planner-side report generation.
- `common.py`
  Shared helpers.

### `tools/lean4-skills/`

Lean-focused operator utilities:

- `analyze_let_usage.py`, `minimize_imports.py`, `solver_cascade.py`, `sorry_analyzer.py`, `try_exact_at_step.py`
  Lean repair and tactic-assistance helpers.
- `find_exact_candidates.py`, `find_golfable.py`, `parse_command_args.py`, `parse_lean_errors.py`
  Search and parser helpers for Lean workflows.
- `check_axioms_inline.sh`, `cycle_tracker.sh`, `find_instances.sh`, `find_usages.sh`, `search_mathlib.sh`, `smart_search.sh`, `unused_declarations.sh`
  Shell helpers for local Lean investigation.
- `test_apply_exact_chains.py`
  Tool self-test for exact-chain application.

### Top-level `tools/*.py`

These are mostly compatibility entrypoints, standalone generators, or thin aliases into the maintained directories.

#### Compatibility / alias wrappers

- `generate_auto_docs.py`, `refresh_blueprint_tags.py`, `refresh_decl_graph.py`, `run_locked_lake_build.py`, `select_openclaw_target.py`, `semantic_block_export.py`, `skynet_v2.py`, `theorem_significance.py`, `update_repo_docs.py`
  Top-level convenience wrappers or preserved entrypoints for maintained tools that now live deeper in the tree.

#### Report/generator entrypoints

- `generate_bridge_candidates.py`, `generate_bridge_thinness_index.py`, `generate_causal_report.py`, `generate_debt_candidates.py`, `generate_llm_debt_prompts.py`, `generate_llm_frontier_prompts.py`, `generate_self_optimization_report.py`, `generate_source_sink_compression.py`, `generate_structural_dedup.py`, `generate_structural_fibers.py`, `generate_surrogate_index.py`, `generate_unification_index.py`, `generate_vacuity_index.py`
  Standalone report or prompt generators around theorem/candidate surfaces.

#### Utility / policy entrypoints

- `build_lock.py`, `check_bipartite_bleed.py`, `check_vacuity_policy.py`, `classify_missing_all.py`, `extract_module_patch.py`, `failure_correction_driver.py`, `graph.py`, `pathing.py`, `plot_decl_graph.py`, `proof_driver.py`, `run_optimization_cycle.py`, `vacuity_planner.py`, `vacuity_policy_config.py`
  Utilities, planners, and older orchestration helpers.

## `scripts/` Lane

This is a smaller compatibility/utilities lane.

### Canonical compatibility CLI

- [scripts/cli.py](../scripts/cli.py)
  Active compatibility CLI exposing:
  - `build-doc-map`
  - `emit-markdown-index`
  - `filter-project-decls`
  - `proof-gap-report`

### Python utilities

- `analysis/filter_project_decls.py`
  Filters project declarations.
- `analysis/lean/catastrophe_surface.py`
  Analysis helper over Lean declaration surfaces.
- `analysis/utils.py`, `utils.py`
  Shared utilities.
- `docs/build_doc_map.py`, `docs/emit_markdown_index.py`, `docs/proof_gap_report.py`
  Documentation and proof-gap inventory tools.
- `docs/convert/common.py`, `docs/convert/main.py`, `docs/convert/modify_latex.py`, `docs/convert/modify_lean.py`, `docs/convert/parse_latex.py`
  LaTeX/Lean conversion helpers.
- `intake/parser.py`
  Intake-side parsing utility.

## Shell Scripts

### Build and environment

- [scripts/build/bootstrap_ubuntu_debian.sh](../scripts/build/bootstrap_ubuntu_debian.sh)
  Bootstrap dependencies on Debian/Ubuntu.
- [scripts/build/install_lean.sh](../scripts/build/install_lean.sh)
  Lean toolchain installer.
- [scripts/build/run_lake_build.sh](../scripts/build/run_lake_build.sh)
  Wrapper around `lake build`.
- [scripts/build/stable-build.sh](../scripts/build/stable-build.sh)
  Stable build recipe.
- [scripts/build/stable-canonical.sh](../scripts/build/stable-canonical.sh)
  Stable canonical build recipe.
- [scripts/run_tests.sh](../scripts/run_tests.sh)
  Project test runner.
- [scripts/setup_dgx_spark_hermes_orchestrator.sh](../scripts/setup_dgx_spark_hermes_orchestrator.sh)
  Setup helper for DGX/Spark/Hermes orchestration.

### Quality and audit

- [scripts/quality/strict-check.sh](../scripts/quality/strict-check.sh)
  Strict repo audit entrypoint.
- [scripts/quality/audit-imports.sh](../scripts/quality/audit-imports.sh)
  Import audit.
- [scripts/quality/audit_namespaces.sh](../scripts/quality/audit_namespaces.sh)
  Namespace audit.
- [scripts/quality/audit_theory.sh](../scripts/quality/audit_theory.sh)
  Theory-layout audit.
- [scripts/quality/ci_baseline.sh](../scripts/quality/ci_baseline.sh)
  CI baseline checks.
- [scripts/quality/clean-unused-imports.sh](../scripts/quality/clean-unused-imports.sh)
  Unused-import cleanup helper.
- [scripts/quality/orphaned-check.sh](../scripts/quality/orphaned-check.sh)
  Orphaned-file or orphaned-surface check.
- [scripts/quality/profile-build.sh](../scripts/quality/profile-build.sh)
  Build profiling wrapper.

### Miscellaneous repo helpers

- [scripts/audit_surrogates.sh](../scripts/audit_surrogates.sh)
  Surrogate-surface audit helper.
- [scripts/enforce_quarantine_imports.sh](../scripts/enforce_quarantine_imports.sh)
  Enforces quarantine import policy.
- [scripts/perf/profile_commands.sh](../scripts/perf/profile_commands.sh)
  Profiles command runtimes.
- [scripts/time_all_modules.sh](../scripts/time_all_modules.sh)
  Times module builds/checks.

### Infra shell wrappers

- `tools/infra/antigravity_with_arango.sh`, `codex_with_arango.sh`, `gemini_with_arango.sh`, `python_with_arango.sh`, `with_arango_env.sh`
  Run specific tools with Arango environment wiring.
- `tools/infra/arango_access_setup.sh`
  Arango setup helper.
- `tools/infra/bwrap_preflight.sh`
  Bubblewrap/sandbox preflight helper.
- `tools/infra/create_evidence_bundle.sh`, `verify_evidence_bundle.sh`, `verify_certificate_hash_binding.sh`, `verify_replay.sh`
  Evidence and replay verification helpers.
- `tools/infra/deploy_spark_models.sh`, `fix_hf_permissions.sh`, `qwen_vllm_service.sh`
  Local model-service deployment and permission helpers.
- `tools/infra/hive_ping.sh`, `hive_with_env.sh`
  Hive runtime helpers.
- `tools/infra/identity_protocol_smoke.sh`
  Identity protocol smoke test.
- `tools/infra/prima_materia_chain.sh`
  Shell wrapper for prima-materia style chain execution.
- `tools/infra/run_gemini_guarded.sh`
  Guarded Gemini CLI execution.

### Lean operator shell helpers

- `tools/lean4-skills/check_axioms_inline.sh`, `cycle_tracker.sh`, `find_instances.sh`, `find_usages.sh`, `search_mathlib.sh`, `smart_search.sh`, `unused_declarations.sh`
  Local Lean inspection helpers.
- [tools/run_leansearch_safe.sh](../tools/run_leansearch_safe.sh)
  Safe wrapper around Lean search tooling.

## Current Migration Reading

The repo is mid-migration from a script ecology toward a cleaner package/API surface.

The current picture is:

- `src/igf/` is the clean greenfield kernel
- `tools/infra/` remains the broad operational shell
- `tools/frontier/`, `tools/leantrail/`, `tools/quality/`, and `tools/docs/` are maintained subsystem lanes
- top-level `tools/*.py`, `cli/`, and `scripts/` still contain compatibility surfaces and historical entrypoints

So the right reading is not “one tool system” but:

1. Lean truth/kernel surfaces
2. Lake-managed operator entrypoints
3. package-owned Python infrastructure
4. maintained operational script lanes
5. compatibility wrappers and legacy-adjacent helpers

## Best Starting Points

For a new operator, start here:

- [tools/README.md](../tools/README.md)
- [tools/infra/README.md](../tools/infra/README.md)
- [lean/DAG/README.md](../lean/DAG/README.md)
- [leantrail/README.md](../leantrail/README.md)
- [docs/ToolingMethodology.md](ToolingMethodology.md)
- [docs/OperatorQuickstart.md](OperatorQuickstart.md)
