# Tool And Script Inventory

Generated: 2026-05-02 from repository filesystem and source headers.

This is an inventory of operational tooling surfaces, not a proof-authority index. Lean theorem modules under `lean/InfoGeometry/**` are intentionally excluded unless they are DAG/agent/docs/script tooling modules.

## Summary

- Inventory entries: 505
- Lake scripts: 21
- Lake libraries/facets surfaced: 13 libraries, 2 package facets

## Lake Commands And Build-Facing Facets

| Kind | Name | What it does |
|---|---|---|
| Lake script | `strictCheck` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `semanticAudit` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `semanticSnapshot` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `proofSession` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `proofPrint` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `graphToBlueprint` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `refreshBlueprintTags` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `bilingualSpineReport` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `dagStatus` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `dagRefresh` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `dagReports` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `dagDoctor` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `dagAll` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `changedVerify` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailConformance` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailExport` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailArangoIngest` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailArangoPhysicsEval` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailFailureHarvest` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailPathLock` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lake script | `leantrailHolePackets` | Entrypoint declared in `lakefile.lean`; dispatches to a Python/shell helper or repo build/report action. |
| Lean library | `DAG` | Lake library target declared in `lakefile.lean`. |
| Lean library | `Agent` | Lake library target declared in `lakefile.lean`. |
| Lean library | `Docs` | Lake library target declared in `lakefile.lean`. |
| Lean library | `Socratic` | Lake library target declared in `lakefile.lean`. |
| Lean library | `InfoGeometry` | Lake library target declared in `lakefile.lean`. |
| Lean library | `InfoGeometryMeta` | Lake library target declared in `lakefile.lean`. |
| Lean library | `InfoGeometryCanonical` | Lake library target declared in `lakefile.lean`. |
| Lean library | `InfoGeometryLLM` | Lake library target declared in `lakefile.lean`. |
| Lean library | `SelfReference` | Lake library target declared in `lakefile.lean`. |
| Lean library | `scripts` | Lake library target declared in `lakefile.lean`. |
| Lean library | `Experimental` | Lake library target declared in `lakefile.lean`. |
| Lean library | `AuditNative` | Lake library target declared in `lakefile.lean`. |
| Lean library | `AuditStrict` | Lake library target declared in `lakefile.lean`. |
| Package facet | `dagMeta` | Generated package artifact facet declared in `lakefile.lean`. |
| Package facet | `dagArtifactsManifest` | Generated package artifact facet declared in `lakefile.lean`. |

## Alexandria corpus tools: tools/alexandria

Entries: 11

| Path | Kind | What it does |
|---|---|---|
| [`tools/alexandria/__init__.py`](../tools/alexandria/__init__.py) | `py` | Alexandria digestion and retrieval pipeline. |
| [`tools/alexandria/alexandria_algorithms.py`](../tools/alexandria/alexandria_algorithms.py) | `py` | Build Alexandria retrieval overlay algorithms from local JSONL artifacts |
| [`tools/alexandria/arango_ingest.py`](../tools/alexandria/arango_ingest.py) | `py` | Ingest Alexandria JSONL artifacts into a second ArangoDB instance |
| [`tools/alexandria/fetch_arxiv_corpus.py`](../tools/alexandria/fetch_arxiv_corpus.py) | `py` | Download a small arXiv corpus into source-aware markdown cache files for Alexandria ingestion |
| [`tools/alexandria/graph_context_rank.py`](../tools/alexandria/graph_context_rank.py) | `py` | Rank Alexandria context with lexical seeds plus graph expansion |
| [`tools/alexandria/render_socratic_dossier.py`](../tools/alexandria/render_socratic_dossier.py) | `py` | Render a Socratic dossier from an Alexandria context packet |
| [`tools/alexandria/repair_lineage.py`](../tools/alexandria/repair_lineage.py) | `py` | Record Alexandria repair lineage for a broken node and compiler-gated candidate |
| [`tools/alexandria/retrieve_context.py`](../tools/alexandria/retrieve_context.py) | `py` | Build a raw Alexandria context packet from local JSONL artifacts |
| [`tools/alexandria/schema.py`](../tools/alexandria/schema.py) | `py` | No top-level description found; inferred utility surface for schema. |
| [`tools/alexandria/semantic_ingest.py`](../tools/alexandria/semantic_ingest.py) | `py` | Digest markdown/text into Alexandria semantic chunks |
| [`tools/alexandria/structural_chunking.py`](../tools/alexandria/structural_chunking.py) | `py` | No top-level description found; inferred utility surface for structural chunking. |

## Archived legacy scripts

Entries: 16

| Path | Kind | What it does |
|---|---|---|
| [`.scripts_archive/bulk_namespace_rewrite.py`](../.scripts_archive/bulk_namespace_rewrite.py) | `py` | No top-level description found; inferred utility surface for bulk namespace rewrite. |
| [`.scripts_archive/gather_cluster_code.py`](../.scripts_archive/gather_cluster_code.py) | `py` | No top-level description found; inferred utility surface for gather cluster code. |
| [`.scripts_archive/namespace_patch_plan.py`](../.scripts_archive/namespace_patch_plan.py) | `py` | No top-level description found; inferred utility surface for namespace patch plan. |
| [`archive/legacy/scripts/agent_doc_gen.py`](../archive/legacy/scripts/agent_doc_gen.py) | `py` | LEGACY compatibility generator for local declaration-neighborhood LaTeX stubs. This script still depends on `tools.graph` and the older graph wrapper lane. Prefer the authoritative blueprint workflow centered on `InfoGeometry.BlueprintTags` and LeanArchitect outputs. |
| [`archive/legacy/scripts/auto_tag.py`](../archive/legacy/scripts/auto_tag.py) | `py` | LEGACY bulk blueprint tag generator from `docs-map/declarations.json`. The supported current workflow is `tools/infra/refresh_blueprint_tags.py`, which uses the public declaration DAG export under `artifacts/dag/`. Keep this script only for compatibility with the older `docs-map`... |
| [`archive/legacy/scripts/autonomous_researcher.py`](../archive/legacy/scripts/autonomous_researcher.py) | `py` | No top-level description found; inferred utility surface for autonomous researcher. |
| [`archive/legacy/scripts/build_theory_manifest.py`](../archive/legacy/scripts/build_theory_manifest.py) | `py` | No top-level description found; inferred utility surface for build theory manifest. |
| [`archive/legacy/scripts/ci_baseline_docsmap.sh`](../archive/legacy/scripts/ci_baseline_docsmap.sh) | `sh` | LEGACY docs-map baseline. This script still exercises the older module-graph lane for compatibility. The authoritative declaration DAG refresh path is `python3 tools/infra/refresh_decl_graph.py`. Steps kept here: 1) full build 2) graph extraction with per-module probe 3) determin... |
| [`archive/legacy/scripts/cluster_theory.py`](../archive/legacy/scripts/cluster_theory.py) | `py` | No top-level description found; inferred utility surface for cluster theory. |
| [`archive/legacy/scripts/generate_library_index.py`](../archive/legacy/scripts/generate_library_index.py) | `py` | LEGACY compatibility generator for the exhaustive LaTeX library index. This script still depends on `tools.graph` and the older graph wrapper surface. Prefer the dedicated `InfoGeometry.BlueprintTags` LeanArchitect lane for exact formal extraction, with curated narrative assemble... |
| [`archive/legacy/scripts/graph.py`](../archive/legacy/scripts/graph.py) | `py` | Legacy/compatibility graph consumer for older InfoGeometry declaration exports. Do not treat this module as the canonical causal-order source of truth. The current authoritative declaration graph lives under `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`, r... |
| [`archive/legacy/scripts/graph_to_blueprint_bulk.py`](../archive/legacy/scripts/graph_to_blueprint_bulk.py) | `py` | LEGACY graph-only generator for bulk `[blueprint]` tags. This script reads `docs-map/graph.json` from the older declaration-graph lane. The supported current workflow is `tools/infra/refresh_blueprint_tags.py` backed by `artifacts/dag/index/decls.jsonl` and the dedicated `InfoGeo... |
| [`archive/legacy/scripts/graph_to_blueprint_inplace.py`](../archive/legacy/scripts/graph_to_blueprint_inplace.py) | `py` | LEGACY bootstrap tool for annotating Lean source with `@[blueprint]` tags from `docs-map/graph.json`. This script belongs to the older graph-only blueprint lane. The supported current workflow is: - `python3 tools/infra/refresh_decl_graph.py` - `python3 tools/infra/refresh_bluepr... |
| [`archive/legacy/scripts/make_graph.py`](../archive/legacy/scripts/make_graph.py) | `py` | No top-level description found; inferred utility surface for make graph. |
| [`archive/legacy/scripts/refactor_plan.py`](../archive/legacy/scripts/refactor_plan.py) | `py` | Generate deterministic graph-driven refactor plan. |
| [`archive/legacy/scripts/skynet.py`](../archive/legacy/scripts/skynet.py) | `py` | No top-level description found; inferred utility surface for skynet. |

## Autonomous math package: tools/infra/autonomous_math

Entries: 10

| Path | Kind | What it does |
|---|---|---|
| [`tools/infra/autonomous_math/__init__.py`](../tools/infra/autonomous_math/__init__.py) | `py` | Autonomous mathematician pipeline modules. |
| [`tools/infra/autonomous_math/compiler_loop.py`](../tools/infra/autonomous_math/compiler_loop.py) | `py` | Compiler/proof repair loop surface. |
| [`tools/infra/autonomous_math/evidence_packet.py`](../tools/infra/autonomous_math/evidence_packet.py) | `py` | Typed evidence packet used between research and formalization phases. |
| [`tools/infra/autonomous_math/lean_coder.py`](../tools/infra/autonomous_math/lean_coder.py) | `py` | Lean coder stage. Writes a draft scaffold under reports/research/generated_lean. It does not auto-import into canonical modules. |
| [`tools/infra/autonomous_math/lean_designer.py`](../tools/infra/autonomous_math/lean_designer.py) | `py` | Lean theorem-design synthesizer. |
| [`tools/infra/autonomous_math/memory_ingest.py`](../tools/infra/autonomous_math/memory_ingest.py) | `py` | Memory ingestion stage for autonomous_math pipeline. |
| [`tools/infra/autonomous_math/pauli_auditor.py`](../tools/infra/autonomous_math/pauli_auditor.py) | `py` | Pauli-style admissibility audit. |
| [`tools/infra/autonomous_math/research_controller.py`](../tools/infra/autonomous_math/research_controller.py) | `py` | End-to-end autonomous mathematician controller (first production lane). |
| [`tools/infra/autonomous_math/socratic_engine.py`](../tools/infra/autonomous_math/socratic_engine.py) | `py` | Socratic/Jungian expansion over evidence packet. |
| [`tools/infra/autonomous_math/socratic_packet.py`](../tools/infra/autonomous_math/socratic_packet.py) | `py` | Packetize Socratic alchemy loop outputs into the autonomous_math evidence format. |

## Build scripts: scripts/build

Entries: 5

| Path | Kind | What it does |
|---|---|---|
| [`scripts/build/bootstrap_ubuntu_debian.sh`](../scripts/build/bootstrap_ubuntu_debian.sh) | `sh` | No top-level description found; inferred utility surface for bootstrap ubuntu debian. |
| [`scripts/build/install_lean.sh`](../scripts/build/install_lean.sh) | `sh` | Optional override for air-gapped environments. Example: LEAN_ELAN_INIT_URL=file:///workspace/cache/elan-init.sh scripts/build/install_lean.sh |
| [`scripts/build/run_lake_build.sh`](../scripts/build/run_lake_build.sh) | `sh` | No top-level description found; inferred utility surface for run lake build. |
| [`scripts/build/stable-build.sh`](../scripts/build/stable-build.sh) | `sh` | Backward-compatible canonical entrypoint now generalized to full-project default. |
| [`scripts/build/stable-canonical.sh`](../scripts/build/stable-canonical.sh) | `sh` | Stable build wrapper to reduce rebuild contention during active development. Usage: scripts/build/stable-canonical.sh scripts/build/stable-canonical.sh InfoGeometry.Canonical.AnalyticalIndex scripts/build/stable-canonical.sh InfoGeometry.Convex.SpinFactorHessian |

## Compatibility CLI package

Entries: 2

| Path | Kind | What it does |
|---|---|---|
| [`cli/__init__.py`](../cli/__init__.py) | `py` | Command entrypoints for local InfoGeometry tooling. |
| [`cli/igf.py`](../cli/igf.py) | `py` | Compatibility wrapper for the package-local igf CLI. |

## Deep research package: tools/infra/deep_research

Entries: 9

| Path | Kind | What it does |
|---|---|---|
| [`tools/infra/deep_research/__init__.py`](../tools/infra/deep_research/__init__.py) | `py` | Official-pattern deep research controller package. Modules: - clarifier: intent clarification - brief_rewriter: execution brief synthesis - planner: plan generation - retriever: source-constrained evidence collection - verifier: coverage/contradiction gate - writer: final synthes... |
| [`tools/infra/deep_research/brief_rewriter.py`](../tools/infra/deep_research/brief_rewriter.py) | `py` | Research-brief rewrite stage for deep research controller. |
| [`tools/infra/deep_research/clarifier.py`](../tools/infra/deep_research/clarifier.py) | `py` | Clarification stage for deep research controller. |
| [`tools/infra/deep_research/common.py`](../tools/infra/deep_research/common.py) | `py` | Shared utilities for deep research controller. |
| [`tools/infra/deep_research/controller.py`](../tools/infra/deep_research/controller.py) | `py` | Official-pattern deep research controller. Implements: 1) clarifier pass 2) research-brief rewrite pass 3) planner pass 4) controlled retrieval pass 5) verifier pass 6) final synthesis pass With explicit source constraints, persisted state, and hard gates. |
| [`tools/infra/deep_research/planner.py`](../tools/infra/deep_research/planner.py) | `py` | Planner stage for deep research controller. |
| [`tools/infra/deep_research/retriever.py`](../tools/infra/deep_research/retriever.py) | `py` | Retriever/reader stage for deep research controller. |
| [`tools/infra/deep_research/verifier.py`](../tools/infra/deep_research/verifier.py) | `py` | Verifier stage for deep research controller. |
| [`tools/infra/deep_research/writer.py`](../tools/infra/deep_research/writer.py) | `py` | Writer stage for deep research controller. |

## Documentation conversion scripts: scripts/docs

Entries: 10

| Path | Kind | What it does |
|---|---|---|
| [`scripts/docs/build_doc_map.py`](../scripts/docs/build_doc_map.py) | `py` | No top-level description found; inferred utility surface for build doc map. |
| [`scripts/docs/convert/__init__.py`](../scripts/docs/convert/__init__.py) | `py` | No top-level description found; inferred utility surface for   init  . |
| [`scripts/docs/convert/common.py`](../scripts/docs/convert/common.py) | `py` | No top-level description found; inferred utility surface for common. |
| [`scripts/docs/convert/main.py`](../scripts/docs/convert/main.py) | `py` | Convert existing leanblueprint file to LeanArchitect format. |
| [`scripts/docs/convert/modify_latex.py`](../scripts/docs/convert/modify_latex.py) | `py` | No top-level description found; inferred utility surface for modify latex. |
| [`scripts/docs/convert/modify_lean.py`](../scripts/docs/convert/modify_lean.py) | `py` | Utilities for adding @[blueprint] attributes to Lean source files. |
| [`scripts/docs/convert/parse_latex.py`](../scripts/docs/convert/parse_latex.py) | `py` | No top-level description found; inferred utility surface for parse latex. |
| [`scripts/docs/emit_markdown_index.py`](../scripts/docs/emit_markdown_index.py) | `py` | No top-level description found; inferred utility surface for emit markdown index. |
| [`scripts/docs/gen_content_auto_tex_from_header.py`](../scripts/docs/gen_content_auto_tex_from_header.py) | `py` | No top-level description found; inferred utility surface for gen content auto tex from header. |
| [`scripts/docs/proof_gap_report.py`](../scripts/docs/proof_gap_report.py) | `py` | Generate a proof-gap report (sorry/axiom) in Markdown and LaTeX. The report is intentionally lightweight and uses only local source text: - finds declarations that are axioms - finds declarations whose proof body currently contains `sorry` This helps stage a clean reimplementatio... |

## Documentation tools: tools/docs

Entries: 4

| Path | Kind | What it does |
|---|---|---|
| [`tools/docs/__init__.py`](../tools/docs/__init__.py) | `py` | Maintained documentation orchestration and generated status surfaces. |
| [`tools/docs/generate_auto_docs.py`](../tools/docs/generate_auto_docs.py) | `py` | No top-level description found; inferred utility surface for generate auto docs. |
| [`tools/docs/refresh_markdown_status.py`](../tools/docs/refresh_markdown_status.py) | `py` | No top-level description found; inferred utility surface for refresh markdown status. |
| [`tools/docs/update_repo_docs.py`](../tools/docs/update_repo_docs.py) | `py` | Refresh tracked repository documentation from trusted semantic exports and Skynet v2 frontier packets. |

## Frontier/proof-session tools: tools/frontier

Entries: 9

| Path | Kind | What it does |
|---|---|---|
| [`tools/frontier/__init__.py`](../tools/frontier/__init__.py) | `py` | Maintained semantic-export and frontier-analysis tooling. |
| [`tools/frontier/compiler_bridge_client.py`](../tools/frontier/compiler_bridge_client.py) | `py` | Call IG.Compiler bridge RPC methods for a Lean source file. |
| [`tools/frontier/extract_module_patch.py`](../tools/frontier/extract_module_patch.py) | `py` | Extract a prompt-ready local module patch around a seed hotspot from the authoritative declaration DAG. |
| [`tools/frontier/proof_print.py`](../tools/frontier/proof_print.py) | `py` | Print the cheapest useful proof-facing view for a Lean file. Defaults to the first goal target at a cursor. |
| [`tools/frontier/proof_runtime.py`](../tools/frontier/proof_runtime.py) | `py` | No top-level description found; inferred utility surface for proof runtime. |
| [`tools/frontier/proof_session.py`](../tools/frontier/proof_session.py) | `py` | Keep one compiler-bridge session open for a file and answer bridge queries from JSON lines on stdin. |
| [`tools/frontier/semantic_block_export.py`](../tools/frontier/semantic_block_export.py) | `py` | Export semantic block JSON for a Lean source file through an external Lean server process. |
| [`tools/frontier/semantic_snapshot.py`](../tools/frontier/semantic_snapshot.py) | `py` | Write one server-backed snapshot packet combining semantic blocks, environment fingerprint, and an optional compiler-bridge query. |
| [`tools/frontier/skynet_v2.py`](../tools/frontier/skynet_v2.py) | `py` | Skynet v2: report-only semantic frontier explorer over trusted semantic block exports. |

## General scripts

Entries: 15

| Path | Kind | What it does |
|---|---|---|
| [`scripts/__init__.py`](../scripts/__init__.py) | `py` | Top-level Python package for active InfoGeometry scripting helpers. This package keeps the still-supported helpers that remain under `scripts/` after archiving the old graph/bootstrap generators into `archive/legacy/`. |
| [`scripts/__main__.py`](../scripts/__main__.py) | `py` | No top-level description found; inferred utility surface for   main  . |
| [`scripts/analysis/filter_project_decls.py`](../scripts/analysis/filter_project_decls.py) | `py` | No top-level description found; inferred utility surface for filter project decls. |
| [`scripts/analysis/lean/__init__.py`](../scripts/analysis/lean/__init__.py) | `py` | No top-level description found; inferred utility surface for   init  . |
| [`scripts/analysis/lean/catastrophe_surface.py`](../scripts/analysis/lean/catastrophe_surface.py) | `py` | Render finite-temperature free-energy catastrophe surfaces. This script builds the same robust-regression-style finite Gibbs model described in the project notes and visualizes the free-energy landscape at: 1) super-critical epsilon 2) critical epsilon 3) sub-critical epsilon It ... |
| [`scripts/analysis/utils.py`](../scripts/analysis/utils.py) | `py` | No top-level description found; inferred utility surface for utils. |
| [`scripts/audit_surrogates.sh`](../scripts/audit_surrogates.sh) | `sh` | Hard gate: stable modules must not depend on surrogate symbols. Allowed location for surrogate placeholders: lean/InfoGeometry/Unstable/** |
| [`scripts/cli.py`](../scripts/cli.py) | `py` | Active compatibility CLI for the remaining scripts/ lane. Archived graph/bootstrap generators now live under archive/legacy/scripts/. |
| [`scripts/enforce_quarantine_imports.sh`](../scripts/enforce_quarantine_imports.sh) | `sh` | No top-level description found; inferred utility surface for enforce quarantine imports. |
| [`scripts/intake/parser.py`](../scripts/intake/parser.py) | `py` | No top-level description found; inferred utility surface for parser. |
| [`scripts/perf/profile_commands.sh`](../scripts/perf/profile_commands.sh) | `sh` | No top-level description found; inferred utility surface for profile commands. |
| [`scripts/run_tests.sh`](../scripts/run_tests.sh) | `sh` | No top-level description found; inferred utility surface for run tests. |
| [`scripts/setup_dgx_spark_hermes_orchestrator.sh`](../scripts/setup_dgx_spark_hermes_orchestrator.sh) | `sh` | Example bootstrap for DGX Spark autonomous prover stack - OpenClaw + NemoClaw runtime - Hermes local learnable skills/memory - Locked Lean diagnostics (no unlocked builds) |
| [`scripts/time_all_modules.sh`](../scripts/time_all_modules.sh) | `sh` | Run from the project root |
| [`scripts/utils.py`](../scripts/utils.py) | `py` | No top-level description found; inferred utility surface for utils. |

## Infrastructure scripts: tools/infra

Entries: 168

| Path | Kind | What it does |
|---|---|---|
| [`tools/infra/__init__.py`](../tools/infra/__init__.py) | `py` | Core maintenance and diagnostic infrastructure for the Spire. |
| [`tools/infra/agentic_policy_lint.py`](../tools/infra/agentic_policy_lint.py) | `py` | Enforce agentic autonomy policy (SOUL/HEARTBEAT/PUBLISH + runtime config). |
| [`tools/infra/alchemical_loop.py`](../tools/infra/alchemical_loop.py) | `py` | Machine-Gated Alchemical Loop |
| [`tools/infra/antigravity_with_arango.sh`](../tools/infra/antigravity_with_arango.sh) | `sh` | No top-level description found; inferred utility surface for antigravity with arango. |
| [`tools/infra/apex_defect_profile.py`](../tools/infra/apex_defect_profile.py) | `py` | Apex-local defect profiler on the SCC-condensed declaration DAG. For a given apex, computes a structured **obstruction dossier** rather than a single importance score. Each dossier contains raw continuous metrics, a discretized severity vector, thin-shell chokepoints, thin transi... |
| [`tools/infra/arango_access_setup.sh`](../tools/infra/arango_access_setup.sh) | `sh` | No top-level description found; inferred utility surface for arango access setup. |
| [`tools/infra/arango_dag_algorithms.py`](../tools/infra/arango_dag_algorithms.py) | `py` | Run DAG graph algorithms over the live Arango topology overlay. This is a derived overlay engine. It does not rewrite raw graph collections and does not replace the Lean-owned DAG exporters. The default input is the lossless raw-DAG SCC overlay: topology_overlay SCC/component ver... |
| [`tools/infra/arango_env.py`](../tools/infra/arango_env.py) | `py` | Shared local Arango environment loading for repo tools. Direct Python entrypoints should behave like ``tools/infra/with_arango_env.sh``: repo-local credentials in ``configs/local/hive_arango.env`` are loaded when the calling shell has not already provided Arango variables. |
| [`tools/infra/arango_fidelity_audit.py`](../tools/infra/arango_fidelity_audit.py) | `py` | Audit how faithful the current Arango graph is to local graph artifacts. The existing `ig_nodes`/`ig_edges` collections are a retrieval projection. This tool makes that explicit by reporting local snapshot counts, known edge leakage, available expression-graph artifacts, and opti... |
| [`tools/infra/arango_gravity_context.py`](../tools/infra/arango_gravity_context.py) | `py` | Build Lean-grounded "gravitational" context from the proven declaration graph. The tool prefers live ArangoDB collections, but falls back to the repo's LeanTrail JSONL export. It emits a compact packet of nearby proven declarations and source excerpts for prover prompts. |
| [`tools/infra/arango_layered_ingest.py`](../tools/infra/arango_layered_ingest.py) | `py` | Ingest hydrated raw graph and topology overlay JSONL into ArangoDB. This keeps the layered tensor-network model intact: - raw nodes/edges are imported one-for-one into raw collections - SCC/topology nodes are imported into a separate overlay collection - projection/quotient edges... |
| [`tools/infra/arango_raw_infotree_graph.py`](../tools/infra/arango_raw_infotree_graph.py) | `py` | Create/probe a named ArangoDB graph for raw_infotree_* collections. This is the handoff point from loss-audited compiler-memory rows to graph analytics tooling. The named graph is an overlay over already imported collections; it does not rewrite or summarize the raw rows. |
| [`tools/infra/arango_raw_infotree_ingest.py`](../tools/infra/arango_raw_infotree_ingest.py) | `py` | Ingest stage raw_infotree_* JSONL exports into ArangoDB. This is intentionally separate from ``arango_layered_ingest.py``. The layered ingester imports the lossless raw DAG dependency substrate. This script imports the compiler-memory ``raw_infotree_*`` sidecar emitted by ``lean/... |
| [`tools/infra/arango_structural_vacuity_audit.py`](../tools/infra/arango_structural_vacuity_audit.py) | `py` | Audit an ArangoDB InfoTree DAG for local theorems with vacuous, trivial-only, foundational-only, or admitted proof-dependency structure. Note: The default mode (max-depth 1) is a one-hop structural screening rather than semantic vacuity or transitive trust analysis. |
| [`tools/infra/artifacts.py`](../tools/infra/artifacts.py) | `py` | No top-level description found; inferred utility surface for artifacts. |
| [`tools/infra/batch_raw_infotree_export.py`](../tools/infra/batch_raw_infotree_export.py) | `py` | Batch RawInfoTree export with LeanDojo-style safety gates. The single-file Lean exporter is intentionally final-forest based: it runs the frontend, then walks ``commandState.infoState.trees`` so tactic surfaces are not missed. That is the right compiler-memory source, but it must... |
| [`tools/infra/build.py`](../tools/infra/build.py) | `py` | No top-level description found; inferred utility surface for build. |
| [`tools/infra/build_changed_lean.py`](../tools/infra/build_changed_lean.py) | `py` | Incremental Lean build helper: detect changed Lean files from git and build only their owner modules under the shared lock. |
| [`tools/infra/build_chiral_patch_hashes.py`](../tools/infra/build_chiral_patch_hashes.py) | `py` | Build conservative chiral patches over the declaration graph. Implements the v1.1 specification for Level 2 spectral navigation. |
| [`tools/infra/build_claim_packet.py`](../tools/infra/build_claim_packet.py) | `py` | No top-level description found; inferred utility surface for build claim packet. |
| [`tools/infra/build_link_ats_dataset.py`](../tools/infra/build_link_ats_dataset.py) | `py` | Build a local ATS-style link-prediction dataset for Lean declarations from verified DAG artifacts and failure memory. |
| [`tools/infra/build_mcbal_library.py`](../tools/infra/build_mcbal_library.py) | `py` | Build a structured local library from downloaded mcbal blog HTML files. |
| [`tools/infra/build_state_first_lane.py`](../tools/infra/build_state_first_lane.py) | `py` | Build the state-first canonical lane (Chunk1..4 + semantic audit) under the shared build lock. |
| [`tools/infra/bwrap_preflight.sh`](../tools/infra/bwrap_preflight.sh) | `sh` | bwrap_preflight.sh Detects whether bubblewrap sandboxing is viable. If not, runs the command directly (fallback mode) unless --require-sandbox is set. Usage: tools/infra/bwrap_preflight.sh -- bash -n tools/infra/hive_with_env.sh tools/infra/bwrap_preflight.sh --require-sandbox --... |
| [`tools/infra/candidate_bridge_packet.py`](../tools/infra/candidate_bridge_packet.py) | `py` | Candidate-bridge packet builder + validator. This is the typed contract for classifying symbolic correspondences into one of: - equivalence - obstruction - discard |
| [`tools/infra/canonical_policy_lint.py`](../tools/infra/canonical_policy_lint.py) | `py` | ⚖️ THE PAULI CANONICAL POLICY LINTER (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script enforces significance and structural policies on the Canonical layer. It uses the Pauli Authority Bridge to distinguish between 'Trivialities' and 'Deep Identi... |
| [`tools/infra/causal_cone_spectrum.py`](../tools/infra/causal_cone_spectrum.py) | `py` | Causal-cone diagnostics on the SCC-condensed declaration DAG. For a given apex node, computes: - Past cone via BFS on the condensed DAG - Shell decomposition by shortest-path distance - RepDepth role overlay per shell (judgment histogram) - Binding witnesses: components receiving... |
| [`tools/infra/changed_verify.py`](../tools/infra/changed_verify.py) | `py` | Verify changed Lean work with one compressed lane: narrow file gates, incremental owner-module builds, and an optional umbrella build. |
| [`tools/infra/check_bipartite_bleed.py`](../tools/infra/check_bipartite_bleed.py) | `py` | Check pairwise anti-bleed directly on the native structural condensation DAG and the public source-sink bipartite correspondence artifact. |
| [`tools/infra/check_gauge_obstruction_tags.py`](../tools/infra/check_gauge_obstruction_tags.py) | `py` | Scan Lean theorem/lemma surfaces for gauge-obstruction nonzero statements and emit anomaly-bearing file tags. |
| [`tools/infra/check_hollow_theorems.py`](../tools/infra/check_hollow_theorems.py) | `py` | ⚖️ THE PAULI AUDITOR: Semantic Fidelity & Hollow Theorem Detector. "Exploration may be Jungian. Closure must be Pauli." This tool detects 'hollow' theorems that typecheck but carry no substantive mathematical content relative to their advertised claim. |
| [`tools/infra/check_representation_depth.py`](../tools/infra/check_representation_depth.py) | `py` | Audit the stable representation spine for direct file-to-file depth skips using the authoritative declaration DAG plus Lean-exported rep-depth metadata. |
| [`tools/infra/check_research_handoff_gate.py`](../tools/infra/check_research_handoff_gate.py) | `py` | ClawCode handoff gate for research-packet + NemoClaw provenance note. |
| [`tools/infra/check_semantic_flow_report.py`](../tools/infra/check_semantic_flow_report.py) | `py` | Run and validate the semantic flow report. Checks output files and required JSON schema keys. |
| [`tools/infra/claim_promote.py`](../tools/infra/claim_promote.py) | `py` | Phase-1 claim promotion guard. Promotes claim.status according to an allowed transition lattice. Enforces witness/formal/audit gates for formal_candidate promotion. |
| [`tools/infra/classify_missing_all.py`](../tools/infra/classify_missing_all.py) | `py` | No top-level description found; inferred utility surface for classify missing all. |
| [`tools/infra/codex_with_arango.sh`](../tools/infra/codex_with_arango.sh) | `sh` | No top-level description found; inferred utility surface for codex with arango. |
| [`tools/infra/create_evidence_bundle.sh`](../tools/infra/create_evidence_bundle.sh) | `sh` | No top-level description found; inferred utility surface for create evidence bundle. |
| [`tools/infra/dag_all.py`](../tools/infra/dag_all.py) | `py` | Run the managed DAG operator lane: status, refresh, reports, doctor. |
| [`tools/infra/dag_config.py`](../tools/infra/dag_config.py) | `py` | No top-level description found; inferred utility surface for dag config. |
| [`tools/infra/dag_doctor.py`](../tools/infra/dag_doctor.py) | `py` | Inspect the managed DAG lane for config, build, artifact, report, and environment issues. |
| [`tools/infra/dag_manifest.py`](../tools/infra/dag_manifest.py) | `py` | Refresh the authoritative DAG lane and write a single manifest stamp for Lake facet tracking. |
| [`tools/infra/dag_refresh.py`](../tools/infra/dag_refresh.py) | `py` | Refresh the authoritative DAG artifacts using the checked-in DAG toolchain config. |
| [`tools/infra/dag_reports.py`](../tools/infra/dag_reports.py) | `py` | Run the managed derived DAG report sequence from dag-toolchain.json. |
| [`tools/infra/dag_status.py`](../tools/infra/dag_status.py) | `py` | Show the active DAG toolchain configuration and authoritative artifact state. |
| [`tools/infra/debug_gravity.py`](../tools/infra/debug_gravity.py) | `py` | Build Lean-grounded "gravitational" context from the proven declaration graph. The tool prefers live ArangoDB collections, but falls back to the repo's LeanTrail JSONL export. It emits a compact packet of nearby proven declarations and source excerpts for prover prompts. |
| [`tools/infra/decl_graph.py`](../tools/infra/decl_graph.py) | `py` | No top-level description found; inferred utility surface for decl graph. |
| [`tools/infra/decl_graph_support.py`](../tools/infra/decl_graph_support.py) | `py` | ⚖️ THE PAULI DECLARATION GRAPH SUPPORT Truth lives in Lean; structure lives in the graph. This module provides high-level GraphProfile objects by combining Lean source metadata with formal topological evidence from the Pauli Authority Bridge. |
| [`tools/infra/deploy_spark_models.sh`](../tools/infra/deploy_spark_models.sh) | `sh` | REFINED DGX SPARK OPERATIONAL RECIPE Deployment script for asymmetric Lean 4 Proof-Orchestration backends. Uses bare-metal vLLM logic for high-precision resource management. |
| [`tools/infra/dgx_spark_hybrid_orchestrator.py`](../tools/infra/dgx_spark_hybrid_orchestrator.py) | `py` | Hybrid DGX Spark orchestrator: deterministic local lane for ATS dataset build -> link-scorer train -> Arango rerank -> optional dual-hypothesis sampler/fuser gate, with optional locked Lean gate. |
| [`tools/infra/dual_hypothesis_sampler.py`](../tools/infra/dual_hypothesis_sampler.py) | `py` | Sample Lean4 hypotheses from base+tuned models using repo-local context (DAG + black books + optional files). |
| [`tools/infra/export_public_release.py`](../tools/infra/export_public_release.py) | `py` | Export a clean public-release tree with third-party exclusions and stubs. |
| [`tools/infra/extract_expr_fingerprints.py`](../tools/infra/extract_expr_fingerprints.py) | `py` | Build lightweight declaration-side ExprFingerprint proxies from decls.jsonl. This is a non-destructive, additive sidecar generator meant for Arango ingestion. It does NOT claim kernel-level term normalization; it computes structural proxies from declaration metadata/text until fu... |
| [`tools/infra/find_vacuous.py`](../tools/infra/find_vacuous.py) | `py` | No top-level description found; inferred utility surface for find vacuous. |
| [`tools/infra/fix_hf_permissions.sh`](../tools/infra/fix_hf_permissions.sh) | `sh` | 🎭 THE PAULI AUDITOR: HF PERMISSION RECLAMATION SCRIPT This script reclaims the 79GB root-locked HuggingFace cache for the goutev user. |
| [`tools/infra/gemini_account_adapter.py`](../tools/infra/gemini_account_adapter.py) | `py` | Account-auth Gemini CLI adapter for single-segment ideation. Input: one JSON object on stdin. Output: one JSON object on stdout with creative_notes + agent status fields. No API-key logic is used here; this assumes local Gemini CLI is already signed in. |
| [`tools/infra/gemini_cli_guard.py`](../tools/infra/gemini_cli_guard.py) | `py` | Rate-limit explicit Gemini CLI use for the theorem-factory workflow. This guard does not run Gemini. It records explicit operator-approved usage so agents do not silently poll or loop through Gemini CLI. |
| [`tools/infra/gemini_with_arango.sh`](../tools/infra/gemini_with_arango.sh) | `sh` | No top-level description found; inferred utility surface for gemini with arango. |
| [`tools/infra/generate_black_books_keyword_report.py`](../tools/infra/generate_black_books_keyword_report.py) | `py` | Build a full lexical index from black-book markdown files only. |
| [`tools/infra/generate_black_books_story_from_keyword_index.py`](../tools/infra/generate_black_books_story_from_keyword_index.py) | `py` | Create a black-books story from full black-books keyword index. |
| [`tools/infra/generate_causal_report.py`](../tools/infra/generate_causal_report.py) | `py` | ⚖️ THE PAULI CAUSAL AUDITOR (ArangoDB SCC-Grounded) Truth lives in Lean; structure lives in the graph. This script replaces legacy networkx topological sorts with formal Causal Stratification from the ArangoDB SCC topology overlay. The 'True Root Order' is defined by the DAG dept... |
| [`tools/infra/generate_equivalence_dictionary.py`](../tools/infra/generate_equivalence_dictionary.py) | `py` | Build a maintained equivalence dictionary for Lean declaration surfaces (variables/functions/lemmas/theorems) from alias and equality/iff relations. |
| [`tools/infra/generate_expr_alpha_dedup.py`](../tools/infra/generate_expr_alpha_dedup.py) | `py` | Compute alpha-equivalence style structural dedup over ExprArangoExport graphs (ig_nodes.jsonl / ig_edges.jsonl), producing declaration-level and subgraph-level compression evidence. |
| [`tools/infra/generate_hypothesis_debt_report.py`](../tools/infra/generate_hypothesis_debt_report.py) | `py` | Rank theorem surfaces by hypothesis/interface debt for selected Lean files. Lean DAG graph evidence is the authority for structural weight; source-text binder cues remain only weak hints. |
| [`tools/infra/generate_keyword_research_report.py`](../tools/infra/generate_keyword_research_report.py) | `py` | Build a genuine full lexical index from all tracked Lean files. This script does not start from hand-picked keywords. It tokenizes every tracked `*.lean` file in the repository, computes corpus-level frequencies, and emits a sorted term index with file hotspots. |
| [`tools/infra/generate_process_flow_report.py`](../tools/infra/generate_process_flow_report.py) | `py` | Generate derived cocycle, comparison, and defect reports from the constitutive process-flow JSONL artifacts. |
| [`tools/infra/generate_projection_coloring.py`](../tools/infra/generate_projection_coloring.py) | `py` | Cluster the lower constructive side of the maintained source-sink graph and project those cluster colors upward onto module carriers and sink families. |
| [`tools/infra/generate_replacement_frontier.py`](../tools/infra/generate_replacement_frontier.py) | `py` | ⚖️ THE PAULI REPLACEMENT FRONTIER (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script identifies 'Replacement Frontier' candidates—theorems that claim significant physical results but lack formal 'Causal Mass' in the ArangoDB DAG. A theorem is a hi... |
| [`tools/infra/generate_repo_story_from_keyword_index.py`](../tools/infra/generate_repo_story_from_keyword_index.py) | `py` | Refactor full Lean keyword indexing into a declaration-grounded repo story. Pipeline: 1) read sorted lexical index from all tracked Lean files 2) pick characteristic terms by profile-aware score 3) deep search all theorem/lemma/axiom blocks for each term 4) emit a research report... |
| [`tools/infra/generate_representation_depth_graph.py`](../tools/infra/generate_representation_depth_graph.py) | `py` | Render the representation-depth spine as a bicategorical graph using Lean-exported depths plus the manual role index. |
| [`tools/infra/generate_semantic_flow_report.py`](../tools/infra/generate_semantic_flow_report.py) | `py` | Generate a semantic flow report over process-flow artifacts using scalable graph algorithms (signed diffusion, entropy production, SCC loop obstruction). |
| [`tools/infra/generate_semantic_quotient.py`](../tools/infra/generate_semantic_quotient.py) | `py` | Coarse-grain the maintained DAG reports into a first semantic quotient: presentation duplicates, transport projections, and suspicious theorem surfaces are contracted into their constructive trunks before reranking knots. |
| [`tools/infra/generate_sorry_equivalence.py`](../tools/infra/generate_sorry_equivalence.py) | `py` | ⚖️ THE PAULI VACUITY STRATIFIER (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script replaces legacy heuristics with formal topological stratification. It classifies theorems into evidence-based risk classes using the Pauli Authority (ArangoDB Live ... |
| [`tools/infra/generate_source_sink_compression.py`](../tools/infra/generate_source_sink_compression.py) | `py` | Build a source-bundle/sink-bundle incidence layer between the atomic declaration DAG and the hydrated module graph. This is the path-compression / theorem-generation view. |
| [`tools/infra/generate_structural_dedup.py`](../tools/infra/generate_structural_dedup.py) | `py` | Generate a native-structure-backed quotient-candidate report over sink surfaces, hydrated carrier shadows, and repeated assumption packets. |
| [`tools/infra/generate_structural_dictionary.py`](../tools/infra/generate_structural_dictionary.py) | `py` | Build a declaration-level structural dictionary over the authoritative DAG. WL refinement is purely structural and blind to Lean tags during clustering; Lean-audited tags are applied only after structural classes are formed. |
| [`tools/infra/generate_structural_fibers.py`](../tools/infra/generate_structural_fibers.py) | `py` | Generate a packet-conditioned structural fiber report over the native condensation topology and the source-sink bipartite correspondence artifact. |
| [`tools/infra/generate_theorem_surface_index.py`](../tools/infra/generate_theorem_surface_index.py) | `py` | Classify exported InfoGeometry declarations into likely constructive derivations, hypothesis bridges, package/reprojection surfaces, surrogate/vacuous surfaces, and neutral definitions using graph-backed structural evidence first. |
| [`tools/infra/generate_theory_cloud_movie.py`](../tools/infra/generate_theory_cloud_movie.py) | `py` | Render the repo DAG as a moving theory-cloud (particle system) using structural and semantic flow fields. |
| [`tools/infra/generate_theory_spire_viz.py`](../tools/infra/generate_theory_spire_viz.py) | `py` | Generate a Spire-layered SVG visualization of the theory graph. Implements a Molecular Dynamics-style relaxation (Gradient Descent) while snapping to Spire layers. Uses meaningful Lean declaration names for labels. |
| [`tools/infra/generate_truth_transport.py`](../tools/infra/generate_truth_transport.py) | `py` | Generate an agent-to-agent truth transport packet from Hermes artifacts. |
| [`tools/infra/graph_hodge_spectrum.py`](../tools/infra/graph_hodge_spectrum.py) | `py` | Global spectral report on the undirected shadow of the declaration DAG. Computes combinatorial Hodge invariants on the *symmetrised* dependency graph (L = D − A, undirected). This is a fast diagnostic tool; it does **not** operate on the SCC-condensed DAG nor compute Drazin or Mo... |
| [`tools/infra/gravitational_retrieval.py`](../tools/infra/gravitational_retrieval.py) | `py` | Extract Gravitational Context from ArangoDB. |
| [`tools/infra/harvest_ground_truth.py`](../tools/infra/harvest_ground_truth.py) | `py` | No top-level description found; inferred utility surface for harvest ground truth. |
| [`tools/infra/hash_signature.py`](../tools/infra/hash_signature.py) | `py` | No top-level description found; inferred utility surface for hash signature. |
| [`tools/infra/hermes_bounded_runner.py`](../tools/infra/hermes_bounded_runner.py) | `py` | Run one bounded Hermes planning cycle over the research packet queue. This runner is intentionally conservative: - it polls the Hermes research packet directory - it selects one draft packet per invocation - it asks the configured planner endpoint for a plan - it writes determini... |
| [`tools/infra/hermes_isolated_adapter.py`](../tools/infra/hermes_isolated_adapter.py) | `py` | No top-level description found; inferred utility surface for hermes isolated adapter. |
| [`tools/infra/hive_arango_queue.py`](../tools/infra/hive_arango_queue.py) | `py` | MotherBee queue-oriented ArangoDB manifold bootstrap for Hive agents. This tool operationalizes the queue/firewall portions of hive.md without inventing new Lean semantics. It provides: - schema initialization for a live Hive database - worker heartbeats for bee registration - qu... |
| [`tools/infra/hive_audit_worker.py`](../tools/infra/hive_audit_worker.py) | `py` | AuditBee worker for first-class Hive audit.semantic tasks. AuditBee is an authority gate, not a promotion worker. It consumes a completed BuildPacket, checks conservative semantic hygiene around the build result and its verification anchor, emits an AuditPacket, and stops there. |
| [`tools/infra/hive_bee.py`](../tools/infra/hive_bee.py) | `py` | Queue-backed autoproof bee for the live Hive manifold. This worker enforces the repo's trust boundary: - retrieve graph-grounded context from the theorem DAG on 8529 first - ask a prover model for a tactic only after retrieval succeeds - verify every tactic through the Lean REPL ... |
| [`tools/infra/hive_build_worker.py`](../tools/infra/hive_build_worker.py) | `py` | BuildBee worker for first-class Hive build.verify tasks. This worker is intentionally narrow: - claims only `task_kind = "build.verify"`; - runs Lake only through `tools/infra/run_locked_lake_build.py`; - emits `BuildPacket` rows for visible lock-wait/running/final state; - leave... |
| [`tools/infra/hive_leansearch_bee.py`](../tools/infra/hive_leansearch_bee.py) | `py` | LeanSearch-backed Hive proof bee lane. Alternative retrieval lane for Hive that keeps the same Lean verification/fossilization pipeline but uses LeanSearch semantic retrieval instead of Arango gravity retrieval. |
| [`tools/infra/hive_packet_build.py`](../tools/infra/hive_packet_build.py) | `py` | Build Hive packets with repo-local defaults and optional schema validation. |
| [`tools/infra/hive_packet_path_runner.py`](../tools/infra/hive_packet_path_runner.py) | `py` | Emit one real Hive packet chain from a bounded Hermes planning cycle. |
| [`tools/infra/hive_packet_validate.py`](../tools/infra/hive_packet_validate.py) | `py` | Validate Hive packet JSON against repo-local machine-readable schemas. |
| [`tools/infra/hive_ping.sh`](../tools/infra/hive_ping.sh) | `sh` | shellcheck disable=SC1090 |
| [`tools/infra/hive_promotion_worker.py`](../tools/infra/hive_promotion_worker.py) | `py` | PromotionBee worker for explicit Hive promotion decisions. Promotion is intentionally separate from proof, build, and audit. This worker consumes `audit.semantic` outputs and emits `PromotionDecisionPacket` rows. It does not mutate Lean files and does not treat conditional audits... |
| [`tools/infra/hive_qi_heartbeat.py`](../tools/infra/hive_qi_heartbeat.py) | `py` | Convert heartbeat log pulses into Hive QI packets, lineage edges, and routed tasks. |
| [`tools/infra/hive_swarm.py`](../tools/infra/hive_swarm.py) | `py` | Multi-role swarm worker for the live Hive queue. Roles: - generator bee: proposes a tactic from graph-grounded context - critic bee: accepts/revises/rejects the proposal before Lean execution - formalizer bee: verifies the tactic through Lean and fossilizes success - auditor bee:... |
| [`tools/infra/hive_with_env.sh`](../tools/infra/hive_with_env.sh) | `sh` | shellcheck disable=SC1090 |
| [`tools/infra/hollow_semantic_auditor.py`](../tools/infra/hollow_semantic_auditor.py) | `py` | ⚖️ HOLLOW SEMANTIC AUDITOR Detecting symbolic inflation and math-meaningless proofs. Protocol: "Exploration may be Jungian. Closure must be Pauli." Goal: Identify theorems that pass the kernel but carry no mathematical content. |
| [`tools/infra/holonomy_auditor.py`](../tools/infra/holonomy_auditor.py) | `py` | Compute LeanTrail holonomy hotspots from a normalized snapshot. Uses telemetry fields when present, otherwise falls back to structural proxies. |
| [`tools/infra/hydrate_arango_topology.py`](../tools/infra/hydrate_arango_topology.py) | `py` | Hydrate raw Arango JSONL graph exports with topology labels. This is deliberately topology-first. It does not infer semantic synonyms. It reads raw node/edge JSONL, computes graph labels from the actual edge topology, and writes a lossless copy with added labels/metrics. |
| [`tools/infra/hypothesis_fuser_and_lean_gate.py`](../tools/infra/hypothesis_fuser_and_lean_gate.py) | `py` | Fuse hypotheses from dual_hypothesis_sampler, rank them, run Lean compile gate, and optionally emit generated Hermes skill templates for accepted candidates. |
| [`tools/infra/identity_protocol_metrics.py`](../tools/infra/identity_protocol_metrics.py) | `py` | tools/infra/identity_protocol_metrics.py Mixed-mode metric evaluator for Identity Protocol v1. - kappa can be real from structural fingerprints (dag_transport.v1) - tau_A/tau_B/tau_C_proxy/epsilon_majorana/delta_M remain proxy in v1 |
| [`tools/infra/identity_protocol_runner.py`](../tools/infra/identity_protocol_runner.py) | `py` | tools/infra/identity_protocol_runner.py Runs Identity Protocol fixtures and writes majorana identity packet artifacts. Local-first: writes artifacts only; heartbeat/queue handles ingestion. |
| [`tools/infra/identity_protocol_smoke.sh`](../tools/infra/identity_protocol_smoke.sh) | `sh` | Shell syntax checks via sandbox when possible, with safe fallback when bwrap is unavailable. |
| [`tools/infra/ingest_chiral_sidecars.py`](../tools/infra/ingest_chiral_sidecars.py) | `py` | Ingest chiral sidecar JSONL artifacts into ArangoDB (immutable runs). One-command pipeline: 1) create collections/indexes if missing 2) import run/patch/spectral docs with onDuplicate=ignore 3) resolve ig_patch_members _to via ig_nodes.name -> _id 4) import patch members and patc... |
| [`tools/infra/ingest_hive_json.py`](../tools/infra/ingest_hive_json.py) | `py` | Extract, normalize, and persist HIVE_JSON packets emitted by HiveLogos. |
| [`tools/infra/injection_build_digest.py`](../tools/infra/injection_build_digest.py) | `py` | Build a cited literature digest markdown from an injection packet. |
| [`tools/infra/injection_capture_gemini_cli.py`](../tools/infra/injection_capture_gemini_cli.py) | `py` | Capture Gemini CLI creative ideation into packet segment cards. This adapter is intentionally account-auth oriented (no API key assumptions): it shells out to a local `gemini` CLI command that is already authenticated via interactive Google account login on the machine. |
| [`tools/infra/injection_chunk_ideate.py`](../tools/infra/injection_chunk_ideate.py) | `py` | Syntactically chunk packet intake text and seed per-segment ideation surfaces. This script is the earliest stage of the gemini-hermes-codex research pipeline: 1) split intake text into syntactic chunks, 2) create/append research segment cards, 3) optionally attach creative ideati... |
| [`tools/infra/injection_common.py`](../tools/infra/injection_common.py) | `py` | Shared helpers for knowledge-injection packet tooling. |
| [`tools/infra/injection_create_packet.py`](../tools/infra/injection_create_packet.py) | `py` | Create a new knowledge injection packet. |
| [`tools/infra/injection_enrich_segment.py`](../tools/infra/injection_enrich_segment.py) | `py` | Update research workflow segments with creative notes and evidence. |
| [`tools/infra/injection_promote.py`](../tools/infra/injection_promote.py) | `py` | Promote injection claim packets between lifecycle lanes. |
| [`tools/infra/injection_research_packet.py`](../tools/infra/injection_research_packet.py) | `py` | Seed a topic-focused deep-research packet in handover/injections. |
| [`tools/infra/injection_slo_report.py`](../tools/infra/injection_slo_report.py) | `py` | Compute injection-pipeline SLO metrics and optional alert thresholds. |
| [`tools/infra/injection_status.py`](../tools/infra/injection_status.py) | `py` | Show lane counts for the knowledge injection subsystem. |
| [`tools/infra/lean_interact_wrapper.py`](../tools/infra/lean_interact_wrapper.py) | `py` | No top-level description found; inferred utility surface for lean interact wrapper. |
| [`tools/infra/leandojo_probe.py`](../tools/infra/leandojo_probe.py) | `py` | Probe the local LeanDojo-v2 installation and emit a deterministic report. |
| [`tools/infra/leandojo_to_hermes_packets.py`](../tools/infra/leandojo_to_hermes_packets.py) | `py` | Convert LeanProgress-style JSONL rows into Hermes research packets. |
| [`tools/infra/leandojo_token_free.py`](../tools/infra/leandojo_token_free.py) | `py` | Use only the token-free LeanDojo-v2 surface and emit deterministic artifacts. |
| [`tools/infra/link_scorer_common.py`](../tools/infra/link_scorer_common.py) | `py` | No top-level description found; inferred utility surface for link scorer common. |
| [`tools/infra/llm_thermo_conformance.py`](../tools/infra/llm_thermo_conformance.py) | `py` | Numerical conformance checks for LLM thermo/operator identities. This script audits runtime trace rows against the finite owner lane identities: - softmax simplex normalization - softmax = Gibbs/KMS weights (when energies are present) - log-partition / Massieu consistency - entro... |
| [`tools/infra/materialize_lossless_infotree.py`](../tools/infra/materialize_lossless_infotree.py) | `py` | Materialize a topology-preserving raw DAG graph for ArangoDB. This builds a layered graph, not a replacement projection: * raw layer: every declaration endpoint and every raw dependency edge from the Lean indexer is preserved one-for-one. * SCC layer: coarse-grained SCC nodes are... |
| [`tools/infra/module_keyword_theory_program.py`](../tools/infra/module_keyword_theory_program.py) | `py` | Module-keyword context program: extract keyword lattice, run deep repo scan, trace trunk->root dependencies, and formulate theorem packets. |
| [`tools/infra/openai_deep_research_datasource_mcp_example.py`](../tools/infra/openai_deep_research_datasource_mcp_example.py) | `py` | Minimal search/fetch MCP datasource for OpenAI Deep Research. This file is a template for the *nested* MCP server used by deep-research jobs. It is not the Codex-facing gateway. Contract: - `search(query)` returns exactly one MCP text content item with JSON payload: {"results": [... |
| [`tools/infra/openai_deep_research_gateway.py`](../tools/infra/openai_deep_research_gateway.py) | `py` | Codex-facing MCP gateway for OpenAI Deep Research. Architecture: 1) Codex-facing MCP tools (`dr_start`, `dr_status`, `dr_result`, ...) 2) Deep-research execution via OpenAI Responses API 3) Optional packet-ingest bridge into `handover/injections/*` This script intentionally keeps... |
| [`tools/infra/pauli_authority_bridge.py`](../tools/infra/pauli_authority_bridge.py) | `py` | ⚖️ THE PAULI AUTHORITY BRIDGE Truth lives in Lean; structure lives in the graph. This module is the sole source of structural truth for the reporting suite. It implements the 'Creation-on-Failure' and 'Self-Healing' authority model. |
| [`tools/infra/plot_decl_graph.py`](../tools/infra/plot_decl_graph.py) | `py` | Export the authoritative declaration DAG into NetworkX artifacts and render readable module-level graph views. |
| [`tools/infra/prima_materia_chain.sh`](../tools/infra/prima_materia_chain.sh) | `sh` | Prima materia chain driver ArXiv/BlackBook -> guarded generative burst -> socratic/invariant packet stubs |
| [`tools/infra/prima_materia_ingest.py`](../tools/infra/prima_materia_ingest.py) | `py` | Phase-1 Prima Materia ingest (ArangoDB). Inputs: - artifact JSON file (required) - optional claims JSON file (list of claim docs) Writes: - prima_materia_artifacts - claims (status default: prima_materia) - graph_morphisms (optional provenance morphism) |
| [`tools/infra/python_with_arango.sh`](../tools/infra/python_with_arango.sh) | `sh` | No top-level description found; inferred utility surface for python with arango. |
| [`tools/infra/qwen_vllm_service.sh`](../tools/infra/qwen_vllm_service.sh) | `sh` | ⚖️ QWEN 35B RESIDENT SERVICE Hardware: Grace Blackwell (GB10) - 121GB VRAM Optimization: Using FlashInfer backend and FP8 KV Cache for Blackwell SM121. MoE: Enabling DeepGEMM via environment variable for optimal expert dispatch. |
| [`tools/infra/refresh_blueprint_tags.py`](../tools/infra/refresh_blueprint_tags.py) | `py` | Refresh the authoritative LeanArchitect-facing blueprint coverage layer from the public declaration metadata export under artifacts/dag/. |
| [`tools/infra/refresh_decl_graph.py`](../tools/infra/refresh_decl_graph.py) | `py` | Refresh the authoritative declaration-DAG artifacts into the public artifacts/dag lane using lean/DAG/Indexer.lean. |
| [`tools/infra/report_rep_layers.py`](../tools/infra/report_rep_layers.py) | `py` | Report L0-L5 representation-layer counts and cross-layer raw edges. |
| [`tools/infra/representation_depth_from_graph.py`](../tools/infra/representation_depth_from_graph.py) | `py` | Derive representation-depth rows from materialized graph artifacts. This is the fast query/report path for the L0-L5 layer contract. Lean remains the source of the `@[rep_depth ...]` tags and raw dependency export; this tool derives direct/closure depth summaries from the already... |
| [`tools/infra/representation_depth_io.py`](../tools/infra/representation_depth_io.py) | `py` | No top-level description found; inferred utility surface for representation depth io. |
| [`tools/infra/rerank_arango_links.py`](../tools/infra/rerank_arango_links.py) | `py` | Retrieve Arango neighborhood candidates around a center declaration and rerank them with local link scorer. |
| [`tools/infra/research_controller.py`](../tools/infra/research_controller.py) | `py` | Closed-loop repo research controller. Implements a practical planner -> retriever -> reader -> critic -> memory loop using existing repository tooling. This is intentionally operational and stateful: each iteration records what was attempted, what evidence was produced, and what ... |
| [`tools/infra/research_digest_worker.py`](../tools/infra/research_digest_worker.py) | `py` | No top-level description found; inferred utility surface for research digest worker. |
| [`tools/infra/research_packet.py`](../tools/infra/research_packet.py) | `py` | Research packet builder + validator. This script defines the typed handoff contract from Hermes deep-research intake to Prompt A / Prompt B routing. |
| [`tools/infra/residue_quarantine.py`](../tools/infra/residue_quarantine.py) | `py` | No top-level description found; inferred utility surface for residue quarantine. |
| [`tools/infra/run_copilot_codex_lean_pipeline.py`](../tools/infra/run_copilot_codex_lean_pipeline.py) | `py` | Run Copilot -> Codex -> Lean pipeline artifact generation. |
| [`tools/infra/run_full_dag_toolchain.py`](../tools/infra/run_full_dag_toolchain.py) | `py` | Run the repo-native DAG/policy toolchain in strict order to avoid stale-artifact contamination. |
| [`tools/infra/run_gemini_guarded.sh`](../tools/infra/run_gemini_guarded.sh) | `sh` | No top-level description found; inferred utility surface for run gemini guarded. |
| [`tools/infra/run_locked_lake_build.py`](../tools/infra/run_locked_lake_build.py) | `py` | Run `lake build` under the shared build lock used by the managed DAG/tooling lane. |
| [`tools/infra/run_proof_prompt_batch.py`](../tools/infra/run_proof_prompt_batch.py) | `py` | Run proof-specialist prompts against the configured proof lane. |
| [`tools/infra/run_socratic_alchemy_batch.py`](../tools/infra/run_socratic_alchemy_batch.py) | `py` | Batch runner for Socratic alchemy loops over multiple seed prompt files. |
| [`tools/infra/run_socratic_alchemy_loop.py`](../tools/infra/run_socratic_alchemy_loop.py) | `py` | Run a guarded Gemini -> Codex -> guarded Gemini Socratic alchemy loop. Features: - N conceptual Gemini/Codex rounds - Codex Lean4 hypothesis generation - N compile/repair cycles - optional lean_interact_wrapper proof-state probe for repair guidance - packetization into autonomous... |
| [`tools/infra/scan_third_party_licenses.py`](../tools/infra/scan_third_party_licenses.py) | `py` | Deep scan repository for third-party licensing/copyright markers. |
| [`tools/infra/score_link_candidates.py`](../tools/infra/score_link_candidates.py) | `py` | Score/rerank link candidates with a local hashed logistic scorer model trained by train_link_scorer.py. |
| [`tools/infra/select_openclaw_target.py`](../tools/infra/select_openclaw_target.py) | `py` | Select actionable OpenClaw targets from graph-coverage gaps first and native structural hotspots second. |
| [`tools/infra/semantic_audit.py`](../tools/infra/semantic_audit.py) | `py` | No top-level description found; inferred utility surface for semantic audit. |
| [`tools/infra/socratic_packet_to_sampler_jsonl.py`](../tools/infra/socratic_packet_to_sampler_jsonl.py) | `py` | Convert a Socratic packet into sampler-style JSONL rows for hypothesis_fuser_and_lean_gate. |
| [`tools/infra/templates/injection_research_packet_spire_pin44.sh`](../tools/infra/templates/injection_research_packet_spire_pin44.sh) | `sh` | Spire Pin(4,4) research packet cycle template. Usage: PACKET_ID=EXT-... TOPIC="..." RAW_TEXT_FILE=/path/raw.txt bash tools/infra/templates/injection_research_packet_spire_pin44.sh Optional env vars: PACKET_ID explicit packet id (default: auto) TOPIC research topic TITLE packet ti... |
| [`tools/infra/timings.py`](../tools/infra/timings.py) | `py` | No top-level description found; inferred utility surface for timings. |
| [`tools/infra/trace_and_retrieve.py`](../tools/infra/trace_and_retrieve.py) | `py` | No top-level description found; inferred utility surface for trace and retrieve. |
| [`tools/infra/train_link_scorer.py`](../tools/infra/train_link_scorer.py) | `py` | Train a local hashed-feature logistic link scorer over ATS dataset rows. No external ML frameworks required. |
| [`tools/infra/validate_raw_infotree_export.py`](../tools/infra/validate_raw_infotree_export.py) | `py` | Validate the stage-1 raw InfoTree export contract. This checks topology preservation surfaces, not mathematical truth. It ensures that an export directory contains the required `raw_infotree_*` files and that parent-child edges reference emitted nodes with sibling indices. |
| [`tools/infra/verify_certificate_hash_binding.sh`](../tools/infra/verify_certificate_hash_binding.sh) | `sh` | No top-level description found; inferred utility surface for verify certificate hash binding. |
| [`tools/infra/verify_evidence_bundle.sh`](../tools/infra/verify_evidence_bundle.sh) | `sh` | No top-level description found; inferred utility surface for verify evidence bundle. |
| [`tools/infra/verify_layered_arango_descent.py`](../tools/infra/verify_layered_arango_descent.py) | `py` | Verify raw-to-overlay-to-raw descent in the layered Arango graph. |
| [`tools/infra/verify_raw_infotree_arango_descent.py`](../tools/infra/verify_raw_infotree_arango_descent.py) | `py` | Verify raw_infotree_* descent invariants in ArangoDB. This verifier is intentionally non-mutating. It checks that the stage ``raw_infotree_*`` projection imported by ``arango_raw_infotree_ingest.py`` is referentially closed and navigable: * tree edges point to real InfoTree nodes... |
| [`tools/infra/verify_replay.sh`](../tools/infra/verify_replay.sh) | `sh` | Spire Replay Verifier (Rubedo Gate 3) Usage: ./verify_replay.sh <theorem_file> <manifest_json> |
| [`tools/infra/with_arango_env.sh`](../tools/infra/with_arango_env.sh) | `sh` | shellcheck disable=SC1090 |

## Lean DAG tools: lean/DAG

Entries: 49

| Path | Kind | What it does |
|---|---|---|
| [`lean/DAG.lean`](../lean/DAG.lean) | `lean` | DAG Umbrella module exporting DAG analysis, search, hydration, and server/report helpers. |
| [`lean/DAG/Analysis.lean`](../lean/DAG/Analysis.lean) | `lean` | Component-level path counts along an adjacency array in a given traversal order. Unified implementation for both forward (dag + topo) and reverse (preds + reverse-topo) directions. |
| [`lean/DAG/Basic.lean`](../lean/DAG/Basic.lean) | `lean` | Collect projection head names in an expression. |
| [`lean/DAG/Betti.lean`](../lean/DAG/Betti.lean) | `lean` | The Homology Engine. It takes a raw Lambda AST (Expr) and computes its topological invariants. |
| [`lean/DAG/BlockExport.lean`](../lean/DAG/BlockExport.lean) | `lean` | " \|\| t.startsWith "--" \|\| t.startsWith "namespace" \|\| t.startsWith "section" \|\| t.startsWith "end" \|\| t.startsWith "universe" \|\| t.startsWith "open" \|\| t.startsWith "attribute" \|\| t.startsWith "set_option"\|\| t.startsWith "local" \|\| t.startsWith "scoped" \|\| t.startsWith "notation"... |
| [`lean/DAG/CategoryBridge.lean`](../lean/DAG/CategoryBridge.lean) | `lean` | Category-Theory Bridge Maps the declaration dependency graph into Mathlib's `CategoryTheory` framework as a coarse **type-head–indexed quiver**. ## Architecture Objects in the quiver are **type-head names** (e.g., `Ring`, `TopologicalSpace`), not individual declaration names. Mor... |
| [`lean/DAG/CategoryBridgeTest.lean`](../lean/DAG/CategoryBridgeTest.lean) | `lean` | CategoryBridge — Regression Test Suite Tests the compositional witness verifier boundary. Coverage: 1. Positive mapped identity case 2. Positive mapped composable-pair witness case 3. Object compatibility failure 4. Missing map skip case 5. No-witness failure case |
| [`lean/DAG/Disassembler.lean`](../lean/DAG/Disassembler.lean) | `lean` | No top-level description found; inferred utility surface for Disassembler. |
| [`lean/DAG/Dominators.lean`](../lean/DAG/Dominators.lean) | `lean` | DAG dominators |
| [`lean/DAG/ExactMorphism.lean`](../lean/DAG/ExactMorphism.lean) | `lean` | Exact Category-Theoretic Morphism Engine Replaces the heuristic WL-hash-based commutativity check in `DAG.Functor` with exact kernel-trusted `isDefEq` verification. ## Architecture 1. **Morphism extraction** runs in `MetaM` using `whnf` + `forallTelescope` to correctly resolve im... |
| [`lean/DAG/ExactMorphismTest.lean`](../lean/DAG/ExactMorphismTest.lean) | `lean` | Exact Morphism Engine — Regression Test Suite Exercises every admission/rejection boundary of the unary fragment engine using toy declarations with known expected behavior. ## Test Coverage 1. Accepted unary morphism 2. Rejected multi-explicit declaration 3. Rejected dependent re... |
| [`lean/DAG/ExportDecls.lean`](../lean/DAG/ExportDecls.lean) | `lean` | `ExportDecls.lean` Compatibility declaration-inventory exporter. This file still exports a filtered JSON inventory of "real" declarations (theorems/defs/axioms/opaque/inductives) from a loaded Lean environment, with optional dependency filtering by namespace. Usage: lake env lean... |
| [`lean/DAG/ExportForwardGraph.lean`](../lean/DAG/ExportForwardGraph.lean) | `lean` | DAG.ExportForwardGraph Compatibility forward-graph exporter. This file still exports a declaration DAG as a simple forward adjacency JSON, but it is no longer the authoritative repository-wide causal-order pipeline. For the current trusted declaration export, use `tools/refresh_d... |
| [`lean/DAG/ExprArangoExport.lean`](../lean/DAG/ExprArangoExport.lean) | `lean` | No top-level description found; inferred utility surface for ExprArangoExport. |
| [`lean/DAG/ExprFingerprint.lean`](../lean/DAG/ExprFingerprint.lean) | `lean` | Spectral fingerprint of a Lean expression. |
| [`lean/DAG/FinalSearch.lean`](../lean/DAG/FinalSearch.lean) | `lean` | Multi-query environment search utility for DAG exploration scripts. Each query prints at most `preview` names plus the total match count. |
| [`lean/DAG/FindFinrank.lean`](../lean/DAG/FindFinrank.lean) | `lean` | We import the base Clifford modules to ensure they are in the environment |
| [`lean/DAG/Functor.lean`](../lean/DAG/Functor.lean) | `lean` | Optimized Categorical Shape Search. Instead of O(N^4) nested loops, we use Hash Joins for O(N^2) or better. **DEPRECATED**: This module uses WL hashing for commutativity checks. Prefer `DAG.ExactMorphism` which uses exact `isDefEq` verification. |
| [`lean/DAG/GlobalDisassembler.lean`](../lean/DAG/GlobalDisassembler.lean) | `lean` | No top-level description found; inferred utility surface for GlobalDisassembler. |
| [`lean/DAG/GraphHodge.lean`](../lean/DAG/GraphHodge.lean) | `lean` | Graph Hodge Theory on the Declaration DAG Given a `TwoComplex` (vertices, oriented edges, triangular faces), this module constructs: - **coboundary operators** `δ₀ = ∂₁ᵀ` and `δ₁ = ∂₂ᵀ` - **combinatorial Laplacians** `Δ₀ = ∂₁ᵀ ∂₁` (on 0-chains) and `Δ₁ = ∂₁ ∂₁ᵀ + ∂₂ᵀ ∂₂` (Hodge L... |
| [`lean/DAG/GroundTruthHarvester.lean`](../lean/DAG/GroundTruthHarvester.lean) | `lean` | No top-level description found; inferred utility surface for GroundTruthHarvester. |
| [`lean/DAG/HolonomyExporter.lean`](../lean/DAG/HolonomyExporter.lean) | `lean` | Extract telemetry packets from a single `InfoTree`. |
| [`lean/DAG/Hydrate.lean`](../lean/DAG/Hydrate.lean) | `lean` | No top-level description found; inferred utility surface for Hydrate. |
| [`lean/DAG/Impact.lean`](../lean/DAG/Impact.lean) | `lean` | No top-level description found; inferred utility surface for Impact. |
| [`lean/DAG/Indexer.lean`](../lean/DAG/Indexer.lean) | `lean` | Schema version for the core indexer artifacts (meta.json, full_graph.json, decls/edges JSONL). |
| [`lean/DAG/IntegrationTest.lean`](../lean/DAG/IntegrationTest.lean) | `lean` | ## 1. Positive Compositional Witness for Forgetful Tower (obj maps) |
| [`lean/DAG/Isomorphism.lean`](../lean/DAG/Isomorphism.lean) | `lean` | The Weisfeiler-Lehman (WL) Isomorphism Engine. **Note**: For commutativity checking, prefer `DAG.ExactMorphism` which uses exact `isDefEq` kernel verification. WL hashing remains useful for structural similarity detection where exact equality is not the question. |
| [`lean/DAG/JsonInstances.lean`](../lean/DAG/JsonInstances.lean) | `lean` | No top-level description found; inferred utility surface for JsonInstances. |
| [`lean/DAG/KernelExtract.lean`](../lean/DAG/KernelExtract.lean) | `lean` | buildGraphFromEnv moved to DAG.Basic |
| [`lean/DAG/LiftNaturality.lean`](../lean/DAG/LiftNaturality.lean) | `lean` | **Deprecated**: WL hash equality on raw sides. Use `isExact` instead. |
| [`lean/DAG/ProcessFlowExport.lean`](../lean/DAG/ProcessFlowExport.lean) | `lean` | No top-level description found; inferred utility surface for ProcessFlowExport. |
| [`lean/DAG/QueryEngine.lean`](../lean/DAG/QueryEngine.lean) | `lean` | No top-level description found; inferred utility surface for QueryEngine. |
| [`lean/DAG/RawInfoTreeExport.lean`](../lean/DAG/RawInfoTreeExport.lean) | `lean` | No top-level description found; inferred utility surface for RawInfoTreeExport. |
| [`lean/DAG/RepresentationDepthExport.lean`](../lean/DAG/RepresentationDepthExport.lean) | `lean` | No top-level description found; inferred utility surface for RepresentationDepthExport. |
| [`lean/DAG/RootOrderExport.lean`](../lean/DAG/RootOrderExport.lean) | `lean` | No top-level description found; inferred utility surface for RootOrderExport. |
| [`lean/DAG/SCC.lean`](../lean/DAG/SCC.lean) | `lean` | Iterative Tarjan DFS. The previous recursive walk could overflow the runtime stack on the full repo graph once refresh reached SCC hydration. |
| [`lean/DAG/Search.lean`](../lean/DAG/Search.lean) | `lean` | Broad namespace suffixes that are poor discriminators in search. |
| [`lean/DAG/SearchByHash.lean`](../lean/DAG/SearchByHash.lean) | `lean` | No top-level description found; inferred utility surface for SearchByHash. |
| [`lean/DAG/SearchCore.lean`](../lean/DAG/SearchCore.lean) | `lean` | Collect all declaration names once. |
| [`lean/DAG/SearchCoreTests.lean`](../lean/DAG/SearchCoreTests.lean) | `lean` | No top-level description found; inferred utility surface for SearchCoreTests. |
| [`lean/DAG/SearchRank.lean`](../lean/DAG/SearchRank.lean) | `lean` | Run one query on a pre-collected declaration-name array. |
| [`lean/DAG/SemanticServerRpc.lean`](../lean/DAG/SemanticServerRpc.lean) | `lean` | No top-level description found; inferred utility surface for SemanticServerRpc. |
| [`lean/DAG/ServerExport.lean`](../lean/DAG/ServerExport.lean) | `lean` | " \|\| t.startsWith "--" \|\| t.startsWith "namespace" \|\| t.startsWith "section" \|\| t.startsWith "end" \|\| t.startsWith "universe" \|\| t.startsWith "open" \|\| t.startsWith "attribute" \|\| t.startsWith "set_option"\|\| t.startsWith "local" \|\| t.startsWith "scoped" \|\| t.startsWith "notation"... |
| [`lean/DAG/SkeletonExport.lean`](../lean/DAG/SkeletonExport.lean) | `lean` | No top-level description found; inferred utility surface for SkeletonExport. |
| [`lean/DAG/StructuralExport.lean`](../lean/DAG/StructuralExport.lean) | `lean` | Stream the structural artifact field-by-field instead of materializing one large top-level `Json` value; the full repo payload is large enough to overflow the runtime stack when serialized in one shot. |
| [`lean/DAG/SubgraphMatch.lean`](../lean/DAG/SubgraphMatch.lean) | `lean` | Subgraph Pattern Matching (VF2-lite) Implements exact subgraph homomorphism search for detecting categorical motifs (commutative squares, spans, cospans, diamonds) in the declaration DAG. ## Algorithm Uses a backtracking constraint-propagation search (VF2-lite) that finds all str... |
| [`lean/DAG/Topo.lean`](../lean/DAG/Topo.lean) | `lean` | No top-level description found; inferred utility surface for Topo. |
| [`lean/DAG/TwoComplex.lean`](../lean/DAG/TwoComplex.lean) | `lean` | 1. Collect Edges |
| [`lean/DAG/Util.lean`](../lean/DAG/Util.lean) | `lean` | Collect all constant names referenced in an expression. |

## Lean agent/protocol tools: lean/Agent

Entries: 5

| Path | Kind | What it does |
|---|---|---|
| [`lean/Agent.lean`](../lean/Agent.lean) | `lean` | Agent Typed proof-state bridge modules for compiler-facing RPC. |
| [`lean/Agent/CompilerBridgeCore.lean`](../lean/Agent/CompilerBridgeCore.lean) | `lean` | No top-level description found; inferred utility surface for CompilerBridgeCore. |
| [`lean/Agent/ProofServerRpc.lean`](../lean/Agent/ProofServerRpc.lean) | `lean` | No top-level description found; inferred utility surface for ProofServerRpc. |
| [`lean/Agent/ProofStateExport.lean`](../lean/Agent/ProofStateExport.lean) | `lean` | No top-level description found; inferred utility surface for ProofStateExport. |
| [`lean/Agent/Protocol.lean`](../lean/Agent/Protocol.lean) | `lean` | 0-based LSP line if available. |

## Lean documentation tools: lean/Docs

Entries: 5

| Path | Kind | What it does |
|---|---|---|
| [`lean/Docs.lean`](../lean/Docs.lean) | `lean` | Docs Umbrella module for documentation-generation library code. Executable helpers such as `Docs.AutoTag` and `Docs.emit_blueprint_tex` are intentionally not imported here because each defines a top-level `main` for `lake env lean --run`. |
| [`lean/Docs/AutoTag.lean`](../lean/Docs/AutoTag.lean) | `lean` | Docs.AutoTag Utilities for extracting blueprint tags from declarations in a namespace. |
| [`lean/Docs/auto_blueprints.lean`](../lean/Docs/auto_blueprints.lean) | `lean` | Docs.auto_blueprints Auto-generated blueprint stubs. |
| [`lean/Docs/emit_blueprint_tex.lean`](../lean/Docs/emit_blueprint_tex.lean) | `lean` | Docs.emit_blueprint_tex LaTeX blueprint emission from DAG-derived skeletons. |
| [`lean/Docs/generated_blueprints.lean`](../lean/Docs/generated_blueprints.lean) | `lean` | Docs.generated_blueprints Generated blueprint aggregation stubs. |

## Lean exploratory scripts: lean/scripts

Entries: 16

| Path | Kind | What it does |
|---|---|---|
| [`lean/scripts/DAG/Exploration/Betti.lean`](../lean/scripts/DAG/Exploration/Betti.lean) | `lean` | scripts.DAG.Exploration.Betti Exploratory script that computes basic homological summaries for declaration expression graphs. |
| [`lean/scripts/DAG/Exploration/Common.lean`](../lean/scripts/DAG/Exploration/Common.lean) | `lean` | No top-level description found; inferred utility surface for Common. |
| [`lean/scripts/DAG/Exploration/CompilerBridgeServer.lean`](../lean/scripts/DAG/Exploration/CompilerBridgeServer.lean) | `lean` | No top-level description found; inferred utility surface for CompilerBridgeServer. |
| [`lean/scripts/DAG/Exploration/Disassembler.lean`](../lean/scripts/DAG/Exploration/Disassembler.lean) | `lean` | scripts.DAG.Exploration.Disassembler Exploratory script for disassembling declarations into expression-graph JSON summaries. |
| [`lean/scripts/DAG/Exploration/FinalSearch.lean`](../lean/scripts/DAG/Exploration/FinalSearch.lean) | `lean` | scripts.DAG.Exploration.FinalSearch Exploratory script that runs final environment search queries for key algebraic tokens. |
| [`lean/scripts/DAG/Exploration/Isomorphism.lean`](../lean/scripts/DAG/Exploration/Isomorphism.lean) | `lean` | scripts.DAG.Exploration.Isomorphism Exploratory script for structural-hash and symmetry comparisons of declaration templates. |
| [`lean/scripts/DAG/Exploration/NaturalityDiagnostics.lean`](../lean/scripts/DAG/Exploration/NaturalityDiagnostics.lean) | `lean` | scripts.DAG.Exploration.NaturalityDiagnostics Diagnostic pass for the `@[spine_functor]` layer that sits above the strict unary morphism engine. Usage: `lake env lean --run lean/scripts/DAG/Exploration/NaturalityDiagnostics.lean [module] [namespace]` Defaults: - module: `InfoGeom... |
| [`lean/scripts/DAG/Exploration/NaturalityPromoter.lean`](../lean/scripts/DAG/Exploration/NaturalityPromoter.lean) | `lean` | scripts.DAG.Exploration.NaturalityPromoter Report-only promoter for `@[spine_functor]` naturality obligations. This does not emit Lean theorem stubs yet; it writes a quarantined Markdown report. Usage: `lake env lean --run lean/scripts/DAG/Exploration/NaturalityPromoter.lean [mod... |
| [`lean/scripts/DAG/Exploration/QueryEngine.lean`](../lean/scripts/DAG/Exploration/QueryEngine.lean) | `lean` | scripts.DAG.Exploration.QueryEngine Exploratory script for querying recursive theorem patterns through the DAG query DSL. |
| [`lean/scripts/DAG/Exploration/Search.lean`](../lean/scripts/DAG/Exploration/Search.lean) | `lean` | scripts.DAG.Exploration.Search Exploratory script for environment search with hybrid and ranked token matching. |
| [`lean/scripts/DAG/Exploration/SearchRank.lean`](../lean/scripts/DAG/Exploration/SearchRank.lean) | `lean` | scripts.DAG.Exploration.SearchRank Exploratory script for ranked token-frequency search over the environment. |
| [`lean/scripts/DAG/Exploration/SemanticBlockExport.lean`](../lean/scripts/DAG/Exploration/SemanticBlockExport.lean) | `lean` | No top-level description found; inferred utility surface for SemanticBlockExport. |
| [`lean/scripts/DAG/Exploration/SemanticBlockServer.lean`](../lean/scripts/DAG/Exploration/SemanticBlockServer.lean) | `lean` | No top-level description found; inferred utility surface for SemanticBlockServer. |
| [`lean/scripts/DAG/Exploration/SemanticSnapshotServer.lean`](../lean/scripts/DAG/Exploration/SemanticSnapshotServer.lean) | `lean` | No top-level description found; inferred utility surface for SemanticSnapshotServer. |
| [`lean/scripts/DAG/Exploration/SquarePromoter.lean`](../lean/scripts/DAG/Exploration/SquarePromoter.lean) | `lean` | scripts.DAG.Exploration.SquarePromoter Generate a quarantined strict-square promotion report outside the checked Lean build. Candidate theorem templates are emitted as Markdown code fences, not as compiled declarations. Usage: `lake env lean --run lean/scripts/DAG/Exploration/Squ... |
| [`lean/scripts/find_convex_lemma.lean`](../lean/scripts/find_convex_lemma.lean) | `lean` | import modules that might contain fderiv/convex lemmas |

## Lean4 skill helper tools: tools/lean4-skills

Entries: 17

| Path | Kind | What it does |
|---|---|---|
| [`tools/lean4-skills/analyze_let_usage.py`](../tools/lean4-skills/analyze_let_usage.py) | `py` | Analyze let binding usage to detect false-positive optimization candidates. Helps avoid the #1 pitfall: inlining let bindings that are used multiple times, which actually INCREASES token count instead of reducing it. |
| [`tools/lean4-skills/check_axioms_inline.sh`](../tools/lean4-skills/check_axioms_inline.sh) | `sh` | check_axioms_inline.sh - Check axioms in Lean 4 files using inline #print axioms Usage: ./check_axioms_inline.sh <file-or-dir-or-pattern> [--verbose] [--exit-zero-on-findings] ./check_axioms_inline.sh src/**/*.lean ./check_axioms_inline.sh MyFile.lean --verbose --report-only ./ch... |
| [`tools/lean4-skills/cycle_tracker.sh`](../tools/lean4-skills/cycle_tracker.sh) | `sh` | Resolve TMPDIR once: honor caller's TMPDIR (macOS always sets it), fall back to /tmp on systems where it is unset (common on Linux). Export so child processes (jq, python3, mktemp) see the same value. |
| [`tools/lean4-skills/find_exact_candidates.py`](../tools/lean4-skills/find_exact_candidates.py) | `py` | Find proof blocks that are good candidates for `exact?` replacement. Scans Lean 4 files for short tactic proofs (2-8 lines) where replacing the entire proof body with `exact?` might find a one-liner. Usage: python3 find_exact_candidates.py File.lean python3 find_exact_candidates.... |
| [`tools/lean4-skills/find_golfable.py`](../tools/lean4-skills/find_golfable.py) | `py` | Find proof-golfing opportunities in Lean 4 files. Identifies optimization patterns with estimated reduction potential. |
| [`tools/lean4-skills/find_instances.sh`](../tools/lean4-skills/find_instances.sh) | `sh` | find_instances.sh - Find type class instances in mathlib Usage: ./find_instances.sh <type-class-name> [--verbose] Searches for instances of a given type class in mathlib. Useful when you need to understand how a type class is instantiated for different types, or to find patterns ... |
| [`tools/lean4-skills/find_usages.sh`](../tools/lean4-skills/find_usages.sh) | `sh` | find_usages.sh - Find all uses of a theorem/lemma/definition in Lean project Usage: ./find_usages.sh <identifier> [directory] Finds all locations where a Lean identifier (theorem, lemma, def, etc.) is used. Excludes the definition itself, focuses on actual usages. Examples: ./fin... |
| [`tools/lean4-skills/minimize_imports.py`](../tools/lean4-skills/minimize_imports.py) | `py` | minimize_imports.py - Remove unused imports from Lean 4 files Usage: ./minimize_imports.py <file> [--dry-run] [--verbose] This script identifies and removes unused imports by: 1. Extracting all imports from the file 2. Temporarily removing each import one at a time 3. Checking if... |
| [`tools/lean4-skills/parse_command_args.py`](../tools/lean4-skills/parse_command_args.py) | `py` | Standalone CLI for the lean4 slash-command parser. Usage: python3 parse_command_args.py <command> [--cwd PATH] -- <raw tail> Exit codes: 0 — success (prints ParseResult JSON to stdout) 1 — usage error (bad CLI arguments) 2 — validation error (prints error JSON to stdout) |
| [`tools/lean4-skills/parse_lean_errors.py`](../tools/lean4-skills/parse_lean_errors.py) | `py` | Parse Lean compiler errors into structured JSON for repair routing. Output schema: { "errorHash": "type_mismatch_42", "errorType": "type_mismatch", "message": "type mismatch at...", "file": "Foo.lean", "line": 42, "column": 10, "goal": "⊢ Continuous f", "localContext": ["h1 : Mea... |
| [`tools/lean4-skills/search_mathlib.sh`](../tools/lean4-skills/search_mathlib.sh) | `sh` | search_mathlib.sh - Find lemmas, theorems, and definitions in mathlib Usage: ./search_mathlib.sh <query> [search-type] [--ignore-case\|-i] Search types: name - Search for declarations by name (default) type - Search for declarations by type signature content - Search file contents... |
| [`tools/lean4-skills/smart_search.sh`](../tools/lean4-skills/smart_search.sh) | `sh` | smart_search.sh - Enhanced Lean theorem search with API integration Usage: ./smart_search.sh <query> [--source=leansearch\|loogle\|mathlib\|all] Searches for Lean theorems using multiple sources: - leansearch: Natural language and semantic search (leansearch.net) - loogle: Type-base... |
| [`tools/lean4-skills/solver_cascade.py`](../tools/lean4-skills/solver_cascade.py) | `py` | Try automated solvers in sequence before resampling with LLM. Handles 40-60% of simple cases mechanically. Cascade order: 1. rfl (definitional equality) 2. simp (simplifier) 3. ring (ring normalization) 4. linarith (linear arithmetic) 5. nlinarith (nonlinear arithmetic) 6. omega ... |
| [`tools/lean4-skills/sorry_analyzer.py`](../tools/lean4-skills/sorry_analyzer.py) | `py` | sorry_analyzer.py - Extract and analyze sorry statements in Lean 4 code Usage: ./sorry_analyzer.py <file-or-directory> [--format=FORMAT \| --format FORMAT] [--interactive] [--include-deps] [--exit-zero-on-findings] This script finds all 'sorry' instances in Lean files and extracts... |
| [`tools/lean4-skills/test_apply_exact_chains.py`](../tools/lean4-skills/test_apply_exact_chains.py) | `py` | Fixture tests for find_apply_exact_chains() in find_golfable.py. Run from the repo root: python3 plugins/lean4/lib/scripts/test_apply_exact_chains.py |
| [`tools/lean4-skills/try_exact_at_step.py`](../tools/lean4-skills/try_exact_at_step.py) | `py` | Try `exact?` at various points in Lean 4 proofs to find one-liner replacements. For each candidate proof block, replaces the tactic body with `exact?`, swaps the source file with the modified version (atomic backup/restore), runs Lean, and captures any suggestion from diagnostics... |
| [`tools/lean4-skills/unused_declarations.sh`](../tools/lean4-skills/unused_declarations.sh) | `sh` | unused_declarations.sh - Find unused theorems, lemmas, and definitions in Lean 4 project Usage: ./unused_declarations.sh [directory] [--exit-zero-on-findings] Finds declarations (theorem, lemma, def) that are never used in the project. Examples: ./unused_declarations.sh ./unused_... |

## LeanTrail application package

Entries: 12

| Path | Kind | What it does |
|---|---|---|
| [`leantrail/__init__.py`](../leantrail/__init__.py) | `py` | LeanTrail package. |
| [`leantrail/api/__init__.py`](../leantrail/api/__init__.py) | `py` | HTTP API surfaces for LeanTrail. |
| [`leantrail/api/server.py`](../leantrail/api/server.py) | `py` | LeanTrail query API server. |
| [`leantrail/backend/__init__.py`](../leantrail/backend/__init__.py) | `py` | Backend services for LeanTrail. |
| [`leantrail/backend/app.py`](../leantrail/backend/app.py) | `py` | Compatibility entrypoint for LeanTrail API. Prefer `python3 -m leantrail.api.server`. |
| [`leantrail/backend/extractor.py`](../leantrail/backend/extractor.py) | `py` | No top-level description found; inferred utility surface for extractor. |
| [`leantrail/backend/indexer.py`](../leantrail/backend/indexer.py) | `py` | Build LeanTrail normalized graph snapshot. |
| [`leantrail/backend/models.py`](../leantrail/backend/models.py) | `py` | No top-level description found; inferred utility surface for models. |
| [`leantrail/backend/normalizer.py`](../leantrail/backend/normalizer.py) | `py` | No top-level description found; inferred utility surface for normalizer. |
| [`leantrail/backend/query_api.py`](../leantrail/backend/query_api.py) | `py` | No top-level description found; inferred utility surface for query api. |
| [`leantrail/backend/rpc_adapter.py`](../leantrail/backend/rpc_adapter.py) | `py` | No top-level description found; inferred utility surface for rpc adapter. |
| [`leantrail/backend/store.py`](../leantrail/backend/store.py) | `py` | No top-level description found; inferred utility surface for store. |

## LeanTrail tools: tools/leantrail

Entries: 9

| Path | Kind | What it does |
|---|---|---|
| [`tools/leantrail/__init__.py`](../tools/leantrail/__init__.py) | `py` | LeanTrail tooling package. |
| [`tools/leantrail/adapters.py`](../tools/leantrail/adapters.py) | `py` | No top-level description found; inferred utility surface for adapters. |
| [`tools/leantrail/arango_ingest.py`](../tools/leantrail/arango_ingest.py) | `py` | Ingest LeanTrail Arango JSONL exports into ArangoDB collections. |
| [`tools/leantrail/arango_physics_evaluator.py`](../tools/leantrail/arango_physics_evaluator.py) | `py` | Evaluate local or ArangoDB LeanTrail neighborhoods as a physical surprisal surface, with optional baseline/candidate delta. |
| [`tools/leantrail/conformance.py`](../tools/leantrail/conformance.py) | `py` | Compare canonical LeanTrail snapshot against another snapshot or external analyzer export (GraphML / Neo4j CSV) and report conformance across counts, SCC signature, query paths, and hotspot overlap. |
| [`tools/leantrail/export.py`](../tools/leantrail/export.py) | `py` | Export LeanTrail snapshot to external analyzer formats. |
| [`tools/leantrail/failure_harvester.py`](../tools/leantrail/failure_harvester.py) | `py` | Harvest process-flow defects into LeanTrail failed transition memory. |
| [`tools/leantrail/hole_packets.py`](../tools/leantrail/hole_packets.py) | `py` | Build ranked hole packets from LeanTrail failure memory and conformance surfaces. |
| [`tools/leantrail/path_lock_registry.py`](../tools/leantrail/path_lock_registry.py) | `py` | Bind/lock path records for LeanTrail edge-state traversal policies. |

## Loose root helper scripts

Entries: 8

| Path | Kind | What it does |
|---|---|---|
| [`find_scc.py`](../find_scc.py) | `py` | No top-level description found; inferred utility surface for find scc. |
| [`fix_splitsupergeometry.sh`](../fix_splitsupergeometry.sh) | `sh` | Add imports |
| [`list_collections.py`](../list_collections.py) | `py` | No top-level description found; inferred utility surface for list collections. |
| [`query_arango.py`](../query_arango.py) | `py` | No top-level description found; inferred utility surface for query arango. |
| [`query_dag.py`](../query_dag.py) | `py` | No top-level description found; inferred utility surface for query dag. |
| [`refactor_namespaces.py`](../refactor_namespaces.py) | `py` | No top-level description found; inferred utility surface for refactor namespaces. |
| [`run_arango_query.py`](../run_arango_query.py) | `py` | No top-level description found; inferred utility surface for run arango query. |
| [`run_arango_query2.py`](../run_arango_query2.py) | `py` | No top-level description found; inferred utility surface for run arango query2. |

## New package kernel: src/igf

Entries: 27

| Path | Kind | What it does |
|---|---|---|
| [`src/igf/__init__.py`](../src/igf/__init__.py) | `py` | igf greenfield kernel package. |
| [`src/igf/artifacts/__init__.py`](../src/igf/artifacts/__init__.py) | `py` | Artifact utilities for igf. |
| [`src/igf/artifacts/compatibility_adapters.py`](../src/igf/artifacts/compatibility_adapters.py) | `py` | No top-level description found; inferred utility surface for compatibility adapters. |
| [`src/igf/artifacts/io.py`](../src/igf/artifacts/io.py) | `py` | No top-level description found; inferred utility surface for io. |
| [`src/igf/artifacts/manifest.py`](../src/igf/artifacts/manifest.py) | `py` | No top-level description found; inferred utility surface for manifest. |
| [`src/igf/cli.py`](../src/igf/cli.py) | `py` | Canonical igf CLI package entrypoint. |
| [`src/igf/config/__init__.py`](../src/igf/config/__init__.py) | `py` | Configuration utilities for igf. |
| [`src/igf/config/env_aliases.py`](../src/igf/config/env_aliases.py) | `py` | No top-level description found; inferred utility surface for env aliases. |
| [`src/igf/config/loader.py`](../src/igf/config/loader.py) | `py` | No top-level description found; inferred utility surface for loader. |
| [`src/igf/config/model.py`](../src/igf/config/model.py) | `py` | No top-level description found; inferred utility surface for model. |
| [`src/igf/config/preflight.py`](../src/igf/config/preflight.py) | `py` | No top-level description found; inferred utility surface for preflight. |
| [`src/igf/graph/__init__.py`](../src/igf/graph/__init__.py) | `py` | Arango graph registry and query helpers for igf. |
| [`src/igf/graph/arango_client.py`](../src/igf/graph/arango_client.py) | `py` | No top-level description found; inferred utility surface for arango client. |
| [`src/igf/graph/arango_http.py`](../src/igf/graph/arango_http.py) | `py` | Package-owned raw HTTP/AQL cursor helpers for graph scripts that should not require python-arango. |
| [`src/igf/graph/collections.py`](../src/igf/graph/collections.py) | `py` | No top-level description found; inferred utility surface for collections. |
| [`src/igf/graph/indexes.py`](../src/igf/graph/indexes.py) | `py` | No top-level description found; inferred utility surface for indexes. |
| [`src/igf/graph/query_registry.py`](../src/igf/graph/query_registry.py) | `py` | Canonical AQL query registry for igf greenfield kernel. All operational queries should be referenced by ID and tested via contract fixtures. |
| [`src/igf/graph/query_runner.py`](../src/igf/graph/query_runner.py) | `py` | No top-level description found; inferred utility surface for query runner. |
| [`src/igf/pipeline/__init__.py`](../src/igf/pipeline/__init__.py) | `py` | Pipeline stages for igf. |
| [`src/igf/pipeline/build.py`](../src/igf/pipeline/build.py) | `py` | No top-level description found; inferred utility surface for build. |
| [`src/igf/pipeline/candidates.py`](../src/igf/pipeline/candidates.py) | `py` | No top-level description found; inferred utility surface for candidates. |
| [`src/igf/pipeline/ingest.py`](../src/igf/pipeline/ingest.py) | `py` | No top-level description found; inferred utility surface for ingest. |
| [`src/igf/pipeline/orchestrator.py`](../src/igf/pipeline/orchestrator.py) | `py` | No top-level description found; inferred utility surface for orchestrator. |
| [`src/igf/pipeline/report.py`](../src/igf/pipeline/report.py) | `py` | No top-level description found; inferred utility surface for report. |
| [`src/igf/pipeline/validate.py`](../src/igf/pipeline/validate.py) | `py` | No top-level description found; inferred utility surface for validate. |
| [`src/igf/pipeline/verify.py`](../src/igf/pipeline/verify.py) | `py` | No top-level description found; inferred utility surface for verify. |
| [`src/igf/policy/__init__.py`](../src/igf/policy/__init__.py) | `py` | Claim-safety policy helpers for igf. |
| [`src/igf/policy/claim_scope.py`](../src/igf/policy/claim_scope.py) | `py` | No top-level description found; inferred utility surface for claim scope. |

## Other Lean tool modules

Entries: 3

| Path | Kind | What it does |
|---|---|---|
| [`lean/AuditNative.lean`](../lean/AuditNative.lean) | `lean` | AuditNative Dedicated Lean-native architecture audit entrypoint. |
| [`lean/AuditStrict.lean`](../lean/AuditStrict.lean) | `lean` | InfoGeometry.AuditStrict Strict repository-admission umbrella. This file keeps the existing representation-depth audit active and exposes the post-hoc admission commands: - `#audit_admission <decl>` - `#audit_admission_file` - `#audit_admission_namespace <ns>` |
| [`lean/ast_export_test.lean`](../lean/ast_export_test.lean) | `lean` | No top-level description found; inferred utility surface for ast export test. |

## Planner package: tools/planner

Entries: 8

| Path | Kind | What it does |
|---|---|---|
| [`tools/planner/__init__.py`](../tools/planner/__init__.py) | `py` | Planner package for vacuity matching, normalization, ranking, and reporting. |
| [`tools/planner/admissibility.py`](../tools/planner/admissibility.py) | `py` | Strict admissibility precheck scaffold logic. |
| [`tools/planner/common.py`](../tools/planner/common.py) | `py` | Shared planner types, constants, and helpers. |
| [`tools/planner/matching.py`](../tools/planner/matching.py) | `py` | Planner matching context and declaration resolution logic. |
| [`tools/planner/normalization.py`](../tools/planner/normalization.py) | `py` | Bridge observation normalization and signal extraction. |
| [`tools/planner/policy.py`](../tools/planner/policy.py) | `py` | Planner policy constants and calibration helpers. |
| [`tools/planner/ranking.py`](../tools/planner/ranking.py) | `py` | Ranking logic for vacuity, owner, replacement, corridor, and declaration plans. |
| [`tools/planner/report.py`](../tools/planner/report.py) | `py` | Markdown and JSON report rendering for vacuity planner outputs. |

## Quality scripts: scripts/quality

Entries: 14

| Path | Kind | What it does |
|---|---|---|
| [`scripts/quality/CheckEnv.lean`](../scripts/quality/CheckEnv.lean) | `lean` | No top-level description found; inferred utility surface for CheckEnv. |
| [`scripts/quality/Header.lean`](../scripts/quality/Header.lean) | `lean` | No top-level description found; inferred utility surface for Header. |
| [`scripts/quality/TestInclude.lean`](../scripts/quality/TestInclude.lean) | `lean` | No top-level description found; inferred utility surface for TestInclude. |
| [`scripts/quality/UseHeader.lean`](../scripts/quality/UseHeader.lean) | `lean` | No top-level description found; inferred utility surface for UseHeader. |
| [`scripts/quality/audit-imports.sh`](../scripts/quality/audit-imports.sh) | `sh` | Script to audit imports in InfoGeometry sources. For each import, comment it out temporarily and test if the file still compiles. If compilation succeeds, the import is likely unnecessary. change to project root then lean subfolder |
| [`scripts/quality/audit_axioms_report.lean`](../scripts/quality/audit_axioms_report.lean) | `lean` | No top-level description found; inferred utility surface for audit axioms report. |
| [`scripts/quality/audit_namespaces.sh`](../scripts/quality/audit_namespaces.sh) | `sh` | audit_namespaces.sh Quick audit for Lean files that are missing a project namespace declaration. Default project namespace: InfoGeometry Usage: bash scripts/audit_namespaces.sh bash scripts/audit_namespaces.sh KLThesis bash scripts/audit_namespaces.sh InfoGeometry ./InfoGeometry ... |
| [`scripts/quality/audit_theory.sh`](../scripts/quality/audit_theory.sh) | `sh` | No top-level description found; inferred utility surface for audit theory. |
| [`scripts/quality/checkdecls.lean`](../scripts/quality/checkdecls.lean) | `lean` | Convert a dotted string (e.g. "Foo.Bar.baz") to a `Name`. |
| [`scripts/quality/ci_baseline.sh`](../scripts/quality/ci_baseline.sh) | `sh` | Current declaration-DAG baseline. This script deliberately avoids the archived docs-map/module_graph lane. Steps kept here: 1) locked public build 2) authoritative declaration-DAG refresh 3) rooted causal-order / coverage refresh 4) missing-All classification refresh |
| [`scripts/quality/clean-unused-imports.sh`](../scripts/quality/clean-unused-imports.sh) | `sh` | Remove import statements flagged as unused in import-unused-list.txt Supports optional dry-run mode and keeps backups of edited files. Usage: $0 [--dry-run] run from lean folder regardless of caller location |
| [`scripts/quality/orphaned-check.sh`](../scripts/quality/orphaned-check.sh) | `sh` | Canonical Lean source roots under lean/ |
| [`scripts/quality/profile-build.sh`](../scripts/quality/profile-build.sh) | `sh` | Profile Lean 4 build times per file using lake and lean --profile |
| [`scripts/quality/strict-check.sh`](../scripts/quality/strict-check.sh) | `sh` | No top-level description found; inferred utility surface for strict check. |

## Quality/audit tools: tools/quality

Entries: 18

| Path | Kind | What it does |
|---|---|---|
| [`tools/quality/__init__.py`](../tools/quality/__init__.py) | `py` | No top-level description found; inferred utility surface for   init  . |
| [`tools/quality/audit_constructivity.py`](../tools/quality/audit_constructivity.py) | `py` | Audit Lean files for exact nonconstructive patterns. |
| [`tools/quality/audit_docstrings.py`](../tools/quality/audit_docstrings.py) | `py` | No top-level description found; inferred utility surface for audit docstrings. |
| [`tools/quality/audit_naming.py`](../tools/quality/audit_naming.py) | `py` | No top-level description found; inferred utility surface for audit naming. |
| [`tools/quality/audit_semantic.py`](../tools/quality/audit_semantic.py) | `py` | Emit a machine-readable semantic audit report for Lean sources. |
| [`tools/quality/audit_style.py`](../tools/quality/audit_style.py) | `py` | No top-level description found; inferred utility surface for audit style. |
| [`tools/quality/check_closure_debt_gate.py`](../tools/quality/check_closure_debt_gate.py) | `py` | Enforce closure-debt no-regression gates on scoped module clusters: no banned tokens and required theorem-anchor presence. |
| [`tools/quality/check_equivalence_dictionary_gate.py`](../tools/quality/check_equivalence_dictionary_gate.py) | `py` | Gate unresolved-token growth in the maintained equivalence dictionary against policy baselines. |
| [`tools/quality/check_frontier_integrity_gate.py`](../tools/quality/check_frontier_integrity_gate.py) | `py` | Hard integrity gate for closure/spectral/sinkhorn frontier clusters. Enforced conditions on configured frontier files: - no `sorry` / `admit` - no `axiom` declarations - no `postulate` declarations |
| [`tools/quality/check_translation_registry.py`](../tools/quality/check_translation_registry.py) | `py` | Gate for theorem-translation registry: require canonical registry rows and proof-anchor declarations on the Lean surface. |
| [`tools/quality/closure_ast_validator.py`](../tools/quality/closure_ast_validator.py) | `py` | Closure AST Validator: Ensures only allowed Lean AST node types are present in closure modules. Requires: ast_export (Lean 4), Python 3.8+ |
| [`tools/quality/closure_debt_auditor.py`](../tools/quality/closure_debt_auditor.py) | `py` | Closure Debt Auditor: Identifies unanchored Lean declarations, theory islands, and holes in the dependency graph. UPGRADED: Uses ArangoDB Authority Bridge for zero-false-positive audit. |
| [`tools/quality/common.py`](../tools/quality/common.py) | `py` | No top-level description found; inferred utility surface for common. |
| [`tools/quality/detect_hollow_theorems.py`](../tools/quality/detect_hollow_theorems.py) | `py` | Hollow Theorem Detector for Lean Codebases Flags theorems/defs as :hollow if: - The conclusion is already known from strictly weaker data - The main bridge is assumed, not proved - Domain objects are only used in assumptions, not in the proof - The proof is trivial (abs_nonneg, r... |
| [`tools/quality/detect_ornamental_hypotheses.py`](../tools/quality/detect_ornamental_hypotheses.py) | `py` | Ornamental Hypothesis Detector for Lean Codebases Flags theorems/defs as :ornamental if: - The main domain object appears only in the assumptions, not in the proof body - There are dead let bindings for domain lemmas that are never used - The proof is just a transport of a previo... |
| [`tools/quality/dvorak_audit.py`](../tools/quality/dvorak_audit.py) | `py` | Dvorak 'Truth and Beauty' Audit |
| [`tools/quality/functorial_invariance_audit.py`](../tools/quality/functorial_invariance_audit.py) | `py` | Trace functorial Core->canopy connectivity and isomorphism corridors to prevent false 'foundational void' audits. |
| [`tools/quality/pauli_seal_audit.py`](../tools/quality/pauli_seal_audit.py) | `py` | Pauli Seal audit (mandatory anti-vacuity directives) |

## Report generators: tools/infra/reports

Entries: 15

| Path | Kind | What it does |
|---|---|---|
| [`tools/infra/reports/__init__.py`](../tools/infra/reports/__init__.py) | `py` | No top-level description found; inferred utility surface for   init  . |
| [`tools/infra/reports/classify_markdown_corpus.py`](../tools/infra/reports/classify_markdown_corpus.py) | `py` | Classify all markdown files in the repository using path + content heuristics and produce JSON/Markdown reports. |
| [`tools/infra/reports/common.py`](../tools/infra/reports/common.py) | `py` | No top-level description found; inferred utility surface for common. |
| [`tools/infra/reports/generate_bilingual_spine_report.py`](../tools/infra/reports/generate_bilingual_spine_report.py) | `py` | Generate a bilingual RedLine spine report: import-closure modules, docstring coverage, and bridge-contract marker presence. |
| [`tools/infra/reports/generate_bridge_candidates.py`](../tools/infra/reports/generate_bridge_candidates.py) | `py` | Generate a report-only bridge-candidate packet directly from a trusted Skynet v2 frontier JSON. |
| [`tools/infra/reports/generate_bridge_thinness_index.py`](../tools/infra/reports/generate_bridge_thinness_index.py) | `py` | No top-level description found; inferred utility surface for generate bridge thinness index. |
| [`tools/infra/reports/generate_debt_candidates.py`](../tools/infra/reports/generate_debt_candidates.py) | `py` | Generate a debt-targeted replacement packet from the tracked surrogate, vacuity, and thin-bridge audits. |
| [`tools/infra/reports/generate_llm_debt_prompts.py`](../tools/infra/reports/generate_llm_debt_prompts.py) | `py` | Generate a dual-lane LLM prompt pair for constructive debt replacement: a creative attack-plan prompt and a critical minimization prompt. |
| [`tools/infra/reports/generate_llm_frontier_prompts.py`](../tools/infra/reports/generate_llm_frontier_prompts.py) | `py` | Generate a dual-lane LLM prompt pair from the current trusted frontier: a creative bridge-proposal prompt and a critical/formal-evaluation prompt. |
| [`tools/infra/reports/generate_markdown_hygiene_report.py`](../tools/infra/reports/generate_markdown_hygiene_report.py) | `py` | Analyze markdown hygiene using content classification + link graph + git recency, with optional exclusion corridors (black books by default). |
| [`tools/infra/reports/generate_repository_surface_index.py`](../tools/infra/reports/generate_repository_surface_index.py) | `py` | Generate a repository-wide file-surface index across Lean, Markdown, Python, and configuration classes. |
| [`tools/infra/reports/generate_self_optimization_report.py`](../tools/infra/reports/generate_self_optimization_report.py) | `py` | No top-level description found; inferred utility surface for generate self optimization report. |
| [`tools/infra/reports/generate_surrogate_index.py`](../tools/infra/reports/generate_surrogate_index.py) | `py` | Generate a tracked surrogate debt index. |
| [`tools/infra/reports/generate_unification_index.py`](../tools/infra/reports/generate_unification_index.py) | `py` | Generate the unification index markdown report. |
| [`tools/infra/reports/generate_vacuity_index.py`](../tools/infra/reports/generate_vacuity_index.py) | `py` | Generate the vacuity index markdown report. |

## Top-level tools

Entries: 39

| Path | Kind | What it does |
|---|---|---|
| [`tools/__init__.py`](../tools/__init__.py) | `py` | TIR (Tool-Integrated Reasoning) layer for the Info-Geometry Spire. |
| [`tools/build_lock.py`](../tools/build_lock.py) | `py` | No top-level description found; inferred utility surface for build lock. |
| [`tools/check_bipartite_bleed.py`](../tools/check_bipartite_bleed.py) | `py` | No top-level description found; inferred utility surface for check bipartite bleed. |
| [`tools/check_vacuity_policy.py`](../tools/check_vacuity_policy.py) | `py` | Vacuity Policy Gate — Layer C of the vacuity enforcement system. Reads the JSON report produced by ``theorem_significance.py`` and enforces the repository policy: any "error"-level violation causes a nonzero exit code. It can also validate that reported levels are consistent with... |
| [`tools/classify_missing_all.py`](../tools/classify_missing_all.py) | `py` | No top-level description found; inferred utility surface for classify missing all. |
| [`tools/extract_module_patch.py`](../tools/extract_module_patch.py) | `py` | No top-level description found; inferred utility surface for extract module patch. |
| [`tools/failure_correction_driver.py`](../tools/failure_correction_driver.py) | `py` | LLM-backed correction driver for optimization-cycle failures. It can render creative/critical repair prompts, invoke optional external LLM wrappers, apply a reviewed replacement theorem block, and fall back to conservative built-in theorem-shape fixes when no reviewed repair surv... |
| [`tools/generate_auto_docs.py`](../tools/generate_auto_docs.py) | `py` | No top-level description found; inferred utility surface for generate auto docs. |
| [`tools/generate_bridge_candidates.py`](../tools/generate_bridge_candidates.py) | `py` | No top-level description found; inferred utility surface for generate bridge candidates. |
| [`tools/generate_bridge_thinness_index.py`](../tools/generate_bridge_thinness_index.py) | `py` | No top-level description found; inferred utility surface for generate bridge thinness index. |
| [`tools/generate_causal_report.py`](../tools/generate_causal_report.py) | `py` | No top-level description found; inferred utility surface for generate causal report. |
| [`tools/generate_debt_candidates.py`](../tools/generate_debt_candidates.py) | `py` | No top-level description found; inferred utility surface for generate debt candidates. |
| [`tools/generate_llm_debt_prompts.py`](../tools/generate_llm_debt_prompts.py) | `py` | No top-level description found; inferred utility surface for generate llm debt prompts. |
| [`tools/generate_llm_frontier_prompts.py`](../tools/generate_llm_frontier_prompts.py) | `py` | No top-level description found; inferred utility surface for generate llm frontier prompts. |
| [`tools/generate_self_optimization_report.py`](../tools/generate_self_optimization_report.py) | `py` | No top-level description found; inferred utility surface for generate self optimization report. |
| [`tools/generate_source_sink_compression.py`](../tools/generate_source_sink_compression.py) | `py` | No top-level description found; inferred utility surface for generate source sink compression. |
| [`tools/generate_structural_dedup.py`](../tools/generate_structural_dedup.py) | `py` | No top-level description found; inferred utility surface for generate structural dedup. |
| [`tools/generate_structural_fibers.py`](../tools/generate_structural_fibers.py) | `py` | No top-level description found; inferred utility surface for generate structural fibers. |
| [`tools/generate_surrogate_index.py`](../tools/generate_surrogate_index.py) | `py` | No top-level description found; inferred utility surface for generate surrogate index. |
| [`tools/generate_unification_index.py`](../tools/generate_unification_index.py) | `py` | No top-level description found; inferred utility surface for generate unification index. |
| [`tools/generate_vacuity_index.py`](../tools/generate_vacuity_index.py) | `py` | No top-level description found; inferred utility surface for generate vacuity index. |
| [`tools/graph.py`](../tools/graph.py) | `py` | Compatibility shim for the archived declaration-graph wrapper. This module is no longer the canonical causal-order surface of the repository. The current authoritative declaration graph lives in `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`, refreshed via ... |
| [`tools/ig.py`](../tools/ig.py) | `py` | Info-Geometry Spire Orchestrator (IG-CLI) Central entrypoint for the Level 3 Greenfield Architecture. |
| [`tools/igf.py`](../tools/igf.py) | `py` | Compatibility wrapper for the package-local igf CLI. |
| [`tools/pathing.py`](../tools/pathing.py) | `py` | No top-level description found; inferred utility surface for pathing. |
| [`tools/plot_decl_graph.py`](../tools/plot_decl_graph.py) | `py` | No top-level description found; inferred utility surface for plot decl graph. |
| [`tools/proof_driver.py`](../tools/proof_driver.py) | `py` | Conservative external proof driver for optimization-cycle quarantine runs. It reads the context JSON, materializes only concrete theorem sketches, and otherwise emits a report explaining why no mutation was attempted. |
| [`tools/refresh_blueprint_tags.py`](../tools/refresh_blueprint_tags.py) | `py` | No top-level description found; inferred utility surface for refresh blueprint tags. |
| [`tools/refresh_decl_graph.py`](../tools/refresh_decl_graph.py) | `py` | No top-level description found; inferred utility surface for refresh decl graph. |
| [`tools/run_leansearch_safe.sh`](../tools/run_leansearch_safe.sh) | `sh` | run_leansearch_safe.sh - Hardened startup for LeanSearch-PS-inference Safe defaults based on hardening pass |
| [`tools/run_locked_lake_build.py`](../tools/run_locked_lake_build.py) | `py` | No top-level description found; inferred utility surface for run locked lake build. |
| [`tools/run_optimization_cycle.py`](../tools/run_optimization_cycle.py) | `py` | Run one safe dry optimization cycle in an isolated git worktree. This runner does not call an LLM; it only materializes a quarantine file, runs a targeted build, and records a manifest. |
| [`tools/select_openclaw_target.py`](../tools/select_openclaw_target.py) | `py` | No top-level description found; inferred utility surface for select openclaw target. |
| [`tools/semantic_block_export.py`](../tools/semantic_block_export.py) | `py` | No top-level description found; inferred utility surface for semantic block export. |
| [`tools/skynet_v2.py`](../tools/skynet_v2.py) | `py` | No top-level description found; inferred utility surface for skynet v2. |
| [`tools/theorem_significance.py`](../tools/theorem_significance.py) | `py` | ⚖️ THE PAULI SIGNIFICANCE AUDITOR (Authority-Grounded) Truth lives in Lean; structure lives in the graph. This script replaces legacy lexical heuristics with formal topological evidence. A theorem is considered significant if it possesses 'Causal Mass'—defined by transitive downs... |
| [`tools/update_repo_docs.py`](../tools/update_repo_docs.py) | `py` | No top-level description found; inferred utility surface for update repo docs. |
| [`tools/vacuity_planner.py`](../tools/vacuity_planner.py) | `py` | Planning-only vacuity planner orchestrator. This tool aggregates read-only compiler bridge payloads, vacuity reports, dependency metadata, and ownership metadata to produce ranked planning outputs: - ranked vacuity candidates - ranked owner candidates - ranked replacement candida... |
| [`tools/vacuity_policy_config.py`](../tools/vacuity_policy_config.py) | `py` | Shared vacuity policy configuration for Layer B and Layer C. This module is the single source of truth for: - strict path prefixes - bridge file hints - attribute-based exemptions - expected violation severity by file context |
