<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](../../docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# Infra Tools

> Status: `local tooling guide`
> Configuration and compiler-entrypoint source review: 2026-11-03 at commit
> `214f7bcf733eaf4720913bc2c082936f2480d3fc`.
> The wider catalog is a navigation aid retained from the earlier guide; this
> review did not execute all tools or services. Source and repo-wide authority
> docs determine current behavior.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

This directory contains the maintained DAG, reporting, and build orchestration entrypoints.
The source of architectural truth is no longer purely Python-side: the native grammar lives in:
- [Architecture.lean](../../lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](../../lean/InfoGeometry/Audit.lean)

For maintained-vs-compatibility status across the whole tooling tree, see
[docs/RepositoryMemoryMap.md](../../docs/RepositoryMemoryMap.md).

The infra layer exists to preserve memory and turn a large formal repository back into an auditable working surface after context has been lost.
Its purpose is to:
- externalize dependency and ownership state from Lean into stable artifacts
- check that adjacent translators and coherence files behave like actual morphism carriers
- expose theorem-surface burden, representation-depth legality, and process-flow pressure
- give CI and humans reproducible structural evidence for the next code-reading pass

It is not here to replace source reading or to legislate mathematical truth from Python alone.

## Example Anchor Corridor

The benchmark corridor documented by this guide is:
- `PositiveMeasure -> Projective.Normalize -> PositiveRayCore -> RelativePotentialCore -> RelativePotentialCountBridge -> RelativeSurprisalOperatorLift`

The infra reports should make four facts recoverable about that corridor:
- the root is representative/count ownership, not a high bridge facade
- normalization debt is owned first as `representativeMassShift`
- the count specialization consumes that ownership as `countMassShift`
- the operator branch ends in `relativeModularHamiltonian_sub_countMassShift_cocycle`, so the cocycle survives averaging instead of being recomputed heuristically

## Managed Operator Surface

The managed DAG lane requires a JSON configuration. At the reviewed commit,
**no `dag-toolchain.json`, `dag-toolchain.local.json`, or tracked template with
that name is present**. Provision a valid local configuration before treating
this lane as runnable from a fresh checkout; this guide does not claim that
setup is complete.

[dag_config.py](dag_config.py) resolves the file in this order:

1. An explicit `--config` argument to a managed command.
2. `DAG_TOOLCHAIN_CONFIG` when no explicit argument was supplied.
3. Repository-root `dag-toolchain.local.json`, if present.
4. Repository-root `dag-toolchain.json`.

The schema is defined by `load_dag_toolchain_config` in that source. It includes
`schemaVersion`, `build`, `authoritativeArtifacts`, `derivedReports`, and
`policies`; build targets, import roots, coverage/leakage policy, and report
sequence must be chosen explicitly. A file's existence alone does not validate
those choices or establish fresh artifacts.

Once configuration and the pinned Lean environment are available, the managed
entrypoints registered in [lakefile.lean](../../lakefile.lean) are:
- `lake script run dagStatus`
- `lake script run dagRefresh`
- `lake script run dagReports`
- `lake script run dagDoctor`
- `lake script run dagAll`
- `lake script run changedVerify`
- `lake script run bilingualSpineReport`

These are thin wrappers over Python entrypoints. `dagReports` also sets a
repo-local Matplotlib cache under `.artifacts/matplotlib`. The five managed
`dag*` commands listed above accept a configuration override, for example
`lake script run dagStatus --config /path/to/prepared-dag-config.json`.
`changedVerify` and `bilingualSpineReport` are separate entrypoints; consult
their own options rather than assuming they share the DAG configuration API.

The report sequence is configuration-driven. The catalog below includes
repository-surface, theorem-surface, bilingual spine, source-sink, causal,
significance, sorry-equivalence, graph-export, and replacement-frontier tools.
Their presence does not mean every local configuration runs all of them or that
stored outputs are synchronized with the current source.
`bilingualSpineReport` can also emit per-module docstring stubs with reference seeds via `--stub-out-dir reports/dag/bilingual-docstring-stubs`.
The managed lane also records timing sidecars for the last authoritative refresh (`artifacts/dag/index/indexer-timing.json`) and the last managed report run (`artifacts/dag/report-timing.json`), which `dagStatus` and `dagDoctor` surface as operator-facing performance summaries.

For the exact operator runbook, including when to use the managed lane, the raw
repair lane, the depth-tag lane, and the process-flow lane, see
[docs/ToolingMethodology.md](../../docs/ToolingMethodology.md).
For the compressed operator surface, see
[docs/OperatorQuickstart.md](../../docs/OperatorQuickstart.md) and
[docs/DAGTroubleshooting.md](../../docs/DAGTroubleshooting.md).
For the end-to-end local topology (authority layer, managed DAG lane, Expr/Arango lane, LeanTrail parity lane, and hypothesis/training lane), see
[docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md](../../docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md).

The experimental Lake facets `:dagMeta` and `:dagArtifactsManifest` are also
defined in [lakefile.lean](../../lakefile.lean). Both explicitly track and pass
repository-root `dag-toolchain.json`; the Python resolver's environment/local
fallback does not remove that facet prerequisite. Inspect the facet and use the
source boundaries below before selecting this heavier lane.

The facet route also needs lock-handoff support before it is a ready locked
entrypoint. When either facet reaches its refresh action through
`run_locked_lake_build.py`, the outer build holds the shared lock while
[refresh_decl_graph.py](refresh_decl_graph.py) acquires it again in a child
process. `--skip-prebuild` skips a build step, not that lock acquisition;
[BuildLock](../build_lock.py) has no cross-process reentry in this route.
Source inspection therefore predicts a self-wait if the refresh action runs.
This was not reproduced by execution, and an up-to-date facet that skips its
refresh action does not exercise that path. Treat lock handoff as separate
implementation work rather than recommending the wrapper as a sufficient fix.

The metadata facet targets `artifacts/dag/index/meta.json`. The manifest facet
writes `artifacts/dag/index/manifest.json` as a stamp for `meta.json`,
`full_graph.json`, `structural-topology.json`, and coverage/leakage sidecar state.
These declarations describe intended outputs, not a successful refresh at the
reviewed commit.

## Canonical Entrypoints

Main DAG refresh and report path:
- `refresh_decl_graph.py`
- `refresh_blueprint_tags.py`
- `reports/generate_bilingual_spine_report.py`
- `run_locked_lake_build.py`
- `dgx_spark_hybrid_orchestrator.py`
- `build_changed_lean.py`
- `generate_theorem_surface_index.py`
- `generate_equivalence_dictionary.py`
- `build_link_ats_dataset.py`
- `train_link_scorer.py`
- `score_link_candidates.py`
- `rerank_arango_links.py`
- `dual_hypothesis_sampler.py`
- `hypothesis_fuser_and_lean_gate.py`
- `reports/generate_repository_surface_index.py`
- `generate_hypothesis_debt_report.py`
- `generate_source_sink_compression.py`
- `generate_causal_report.py`
- `check_gauge_obstruction_tags.py`
- `check_bipartite_bleed.py`
- `generate_structural_dedup.py`
- `generate_structural_dictionary.py`
- `generate_structural_fibers.py`
- `generate_semantic_quotient.py`
- `generate_projection_coloring.py`
- `select_openclaw_target.py`
- `canonical_policy_lint.py`
- `agentic_policy_lint.py`
- `module_keyword_theory_program.py`
- `generate_replacement_frontier.py`
- `classify_missing_all.py`

Research-injection pipeline surfaces:
- `injection_create_packet.py`
- `injection_research_packet.py`
- `injection_chunk_ideate.py`
- `injection_capture_gemini_cli.py`
- `gemini_account_adapter.py`
- `injection_enrich_segment.py`
- `injection_build_digest.py`
- `injection_promote.py`
- `injection_status.py`
- `openai_deep_research_gateway.py` (Codex-facing MCP gateway for OpenAI DR jobs)
- `openai_deep_research_datasource_mcp_example.py` (nested `search`/`fetch` datasource template)
- `deep_research/controller.py` (official staged controller: clarify -> rewrite -> planner -> retriever -> verifier -> writer, with source constraints and hard gates)
- `research_packet.py` (typed Hermes intake packet builder/validator)
- `candidate_bridge_packet.py` (typed candidate-map packet builder/validator for equivalence/obstruction/discard classification)
- `check_research_handoff_gate.py` (ClawCode gate: packet + NemoClaw provenance note)
- `research_controller.py` (closed-loop planner/retriever/reader/critic loop with strict gating and state memory)
- `autonomous_math/research_controller.py` (multi-phase stack: clarify -> rewrite -> deep research -> Socratic -> Pauli audit -> Lean design/coder -> compiler loop -> memory ingest)

Runtime LLM theorem-conformance surface:
- `llm_thermo_conformance.py` (numerical residual audit for finite Gibbs/softmax, partition, free-energy, and defect identities on JSONL traces; it does not test a KMS boundary condition)

Release/compliance surfaces:
- `create_evidence_bundle.sh` (deterministic archive + checksum + certificate bundle; optional OpenTimestamps stamping)
- `verify_evidence_bundle.sh` (checksum verification for bundle outputs)
- `export_public_release.py` (clean public-release export with third-party exclusion stubs)
- `scan_third_party_licenses.py` (deep copyright/license marker scan and report generation)

Gemini passthrough arg guard:
- `injection_capture_gemini_cli.py` and `gemini_account_adapter.py` strip any
  passthrough arg containing `prompt_cache_retention` and emit a warning to
  `stderr`; this prevents legacy cache-retention flags from breaking modern
  Gemini/OpenAI-compatible backends.
- This guard protects repo-side Gemini invocations only. If Codex itself emits
  `Error running remote compact task` for `prompt_cache_retention`, that
  failure is outside this repo-side guard. Preserve the error and environment
  details for diagnosis; the former `docs/CodexTroubleshooting.md` pointer is
  not a tracked document at the reviewed commit.

Stable spine supplements:
- `check_representation_depth.py`
- `generate_representation_depth_graph.py`

Visualization and I/O:
- `plot_decl_graph.py`
- `representation_depth_io.py`

Process-flow supplements:
- `lean/DAG/ProcessFlowExport.lean`
- `generate_process_flow_report.py`

Arango expression graph supplement:
- `lean/DAG/ExprArangoExport.lean` (Arango-ready decl+Expr DAG export with De Bruijn `bound_by` edges)
- `tools/leantrail/arango_ingest.py` (loads `ig_nodes.jsonl` / `ig_edges.jsonl` into ArangoDB)

## Tool Families

Use the infra tools by role, not as one undifferentiated report pile:

- build/orchestration
  - `run_locked_lake_build.py`
  - `dgx_spark_hybrid_orchestrator.py`
  - `build_changed_lean.py` (incremental owner-module builds from git-changed Lean files; avoids umbrella rebuild loops by default)
- declaration graph refresh
  - `refresh_decl_graph.py`
  - `refresh_blueprint_tags.py`
- theorem-surface and canonical burden
  - `reports/generate_repository_surface_index.py` (typed inventory of tracked Lean/Markdown/Python/config surfaces via `git ls-files`; linear in file count; optional `--include-untracked` mode for exhaustive local scans)
  - `generate_theorem_surface_index.py`
  - `generate_equivalence_dictionary.py` (builds a maintained equivalence/alias dictionary across variables, functions, lemmas, and theorems from Lean declaration surfaces, merging optional curated pairs from `docs/NameEquivalenceRegistry.json`; emits `reports/dag/equivalence-dictionary.{json,md}`)
  - `tools/quality/check_equivalence_dictionary_gate.py` (CI threshold gate for unresolved-token growth in the generated equivalence dictionary)
  - `build_link_ats_dataset.py` (builds ATS-style local link-prediction dataset with paired `.lean` text snippets + `.olean`-derived structural signals from verified DAG edges and LeanTrail failure memory)
  - `train_link_scorer.py` (trains local hashed logistic scorer on ATS rows; no torch dependency)
  - `score_link_candidates.py` (scores/reranks candidate link rows using trained local scorer)
  - `rerank_arango_links.py` (retrieves Arango neighborhood candidates around a center declaration and reranks them with the local scorer in one step)
  - `dual_hypothesis_sampler.py` (samples candidate Lean hypotheses from base+tuned providers under repo-local context, including DAG and black-book context; providers: `openai-chat` for local OpenAI-compatible endpoints, or `gemini-cli` for account-auth Gemini CLI)
  - `hypothesis_fuser_and_lean_gate.py` (fuses/ranks sampled hypotheses, runs `lake env lean` gate on top candidates, and can emit generated Hermes skill templates)
  - `generate_hypothesis_debt_report.py` (ranks theorem/lemma surfaces by hypothesis/interface debt; defaults to synthesis capstones and emits top-20 JSON/Markdown)
  - `canonical_policy_lint.py`
  - `agentic_policy_lint.py` (enforces SOUL/HEARTBEAT/PUBLISH policy files, symbol-first protocol linkage, and runtime two-key publish gate settings)
  - `generate_replacement_frontier.py` (cross-references surface index, DAG, depth tags, and vacuity scores to rank replacement candidates)

- causal/ownership shape
  - `generate_source_sink_compression.py`
  - `generate_causal_report.py`
  - `generate_expr_alpha_dedup.py` (alpha-equivalence style structural dedup over ExprArangoExport graphs; declaration/subgraph compression report)
  - `check_gauge_obstruction_tags.py` (tags files/declarations carrying `gaugeObstruction` nonzero/zero assumptions and conclusions; emits anomaly-bearing classification reports; supports strict CI flags `--fail-on-any-anomaly-bearing` and `--fail-on-anomaly-bearing-path <prefix>`)
  - `check_bipartite_bleed.py`
  - `generate_structural_dedup.py`
  - `generate_structural_fibers.py`
  - `generate_semantic_quotient.py`
  - `generate_projection_coloring.py`
- apex-local obstruction diagnostics
  - `causal_cone_spectrum.py` (SCC-condensed causal cones, shells, binding witnesses, masses)
  - `apex_defect_profile.py` (structured obstruction dossiers per apex)
  - `graph_hodge_spectrum.py` (global spectral/Hodge report on undirected shadow)
- representation-depth grammar
  - `check_representation_depth.py`
  - `generate_representation_depth_graph.py`
  - `representation_depth_io.py` (shared I/O: loads depth indices, Lean tags JSON, interval labels)
- visualization
  - `plot_decl_graph.py` (NetworkX GraphML, SVG, burndown charts; frontier category coloring)
- classification and structural
  - `classify_missing_all.py`
  - `generate_structural_dictionary.py`
  - `reports/classify_markdown_corpus.py` (repo-wide markdown type classification with confidence scores)
  - `reports/generate_markdown_hygiene_report.py` (staleness/orphan/readme hygiene audit with Black Books excluded by default)
- full-lean keyword indexing and story synthesis
  - `generate_keyword_research_report.py` (indexes all tracked Lean files; sorted lexical frequency + hotspot files)
  - `generate_repo_story_from_keyword_index.py` (characteristic-term selection + deep theorem/lemma/axiom search + story synthesis)
  - `query_external_corpus.py` (search mirrored external corpora by keyword/declaration name; accepts --corpus and --list)
  - `module_keyword_theory_program.py` (module-name keyword extraction + full-repo keyword scan + trunk→root dependency tracing + theorem-packet draft synthesis with literature context)
- closed-loop deep-research control
  - `deep_research/controller.py` (official Responses tool stack: web_search/file_search/mcp with stateful planning and verification gates)
  - `research_packet.py` (typed packet contract from Hermes intake to Prompt A/B)
  - `candidate_bridge_packet.py` (typed bridge packet contract that forces candidate symbolic maps into equivalence/obstruction/discard outcomes)
  - `check_research_handoff_gate.py` (mandatory packet+provenance admission gate for closure)
  - `research_controller.py` (iterative stateful controller that composes keyword retrieval, declaration-grounded extraction, vacuity verification, and confidence-gated convergence)
- autonomous mathematician stack
  - `autonomous_math/evidence_packet.py`
  - `autonomous_math/socratic_engine.py`
  - `autonomous_math/pauli_auditor.py`
  - `autonomous_math/lean_designer.py`
  - `autonomous_math/lean_coder.py`
  - `autonomous_math/compiler_loop.py`
  - `autonomous_math/memory_ingest.py`
  - `autonomous_math/research_controller.py`
- black-books keyword indexing and story synthesis
  - `generate_black_books_keyword_report.py` (indexes black-book markdown corpus; sorted lexical frequency + chapter hotspots)
  - `generate_black_books_story_from_keyword_index.py` (profile-aware characteristic terms + deep excerpt search + story synthesis)
- process-flow and coherence pressure
  - `lean/DAG/ProcessFlowExport.lean`
  - `generate_process_flow_report.py`

No-cloud/no-key note for hypothesis loop:
- `dgx_spark_hybrid_orchestrator.py` and `dual_hypothesis_sampler.py` support local OpenAI-compatible model servers with placeholder API values (for example `EMPTY`) and also support `gemini-cli` account-auth execution paths.

### Closed-Loop Research Controller

Minimal run (artifact-driven; no forced refresh):

```bash
python3 tools/infra/research_controller.py \
  --goal "map Type III modular support closure gaps" \
  --profile methodology \
  --include-significance \
  --run-vacuity-gate \
  --refresh-policy missing
```

Refresh-heavy run (recompute stale surfaces before critique):

```bash
python3 tools/infra/research_controller.py \
  --goal "derive theorem-target map for RN/Connes bridge" \
  --profile physics \
  --include-significance \
  --refresh-policy stale \
  --max-artifact-age-hours 12
```

The controller writes a full JSON memory trace under `reports/research/`
including iteration-by-iteration subtasks, command results, extracted metrics,
critique verdicts, blockers, and unresolved questions.

### Hermes Intake Packet Contract

Schema:

```bash
tools/schema/research_packet.json
```

Build packet from deep-research state:

```bash
python3 tools/infra/research_packet.py build \
  --state reports/research/deep-research-state-<...>.json \
  --out quarantine/hermes_memory/research_packets/<packet>.json
```

Validate packet:

```bash
python3 tools/infra/research_packet.py validate \
  --packet quarantine/hermes_memory/research_packets/<packet>.json
```

ClawCode admission gate:

```bash
python3 tools/infra/check_research_handoff_gate.py \
  --packet quarantine/hermes_memory/research_packets/<packet>.json \
  --nemoclaw-note <nemoclaw-note.md>
```

### Candidate Bridge Packet Contract

Schema:

```bash
tools/schema/candidate_bridge_packet.json
```

Build packet:

```bash
python3 tools/infra/candidate_bridge_packet.py build \
  --out reports/research/bridge-packets/<packet>.json \
  --source-owner <source-owner-surface> \
  --target-owner <target-owner-surface> \
  --claimed-invariant "<invariant>" \
  --map-expression "<explicit map>" \
  --outcome-class obstruction \
  --theorem-name <target-theorem> \
  --mismatch-name <mismatch-object> \
  --mismatch-gap "<preservation gap>"
```

Validate packet:

```bash
python3 tools/infra/candidate_bridge_packet.py validate \
  --packet reports/research/bridge-packets/<packet>.json
```

### Local Link-Scorer Quickstart

```bash
python3 tools/infra/build_link_ats_dataset.py \
  --out reports/training/link_ats_dataset.jsonl \
  --stats-out reports/training/link_ats_dataset.stats.json

python3 tools/infra/train_link_scorer.py \
  --dataset reports/training/link_ats_dataset.jsonl \
  --model-out reports/training/link_scorer_model.npz \
  --metrics-out reports/training/link_scorer_metrics.json

python3 tools/infra/score_link_candidates.py \
  --model reports/training/link_scorer_model.npz \
  --input reports/training/link_ats_dataset.jsonl \
  --out reports/training/link_candidate_scores.jsonl \
  --top-k 200

python3 tools/infra/rerank_arango_links.py \
  --mode local \
  --input artifacts/leantrail/arango \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --radius 2 \
  --model reports/training/link_scorer_model.npz \
  --out reports/training/arango_link_rerank.json \
  --top-k 100
```

### DGX Spark Hybrid Orchestrator

Use this when you want one deterministic local execution lane for:
- optional locked Lean gate
- ATS dataset build
- local link-scorer training
- Arango neighborhood rerank

Hermes remains an intake/discovery layer, while this orchestrator owns training/rerank execution.

```bash
python3 tools/infra/dgx_spark_hybrid_orchestrator.py \
  --profile dgx-spark \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --mode local \
  --arango-input artifacts/leantrail/arango \
  --out-dir reports/training/dgx_hybrid
```

For lighter local iteration:

```bash
python3 tools/infra/dgx_spark_hybrid_orchestrator.py \
  --profile hermes-hybrid \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --skip-locked-build
```

Full one-command lane (link scorer + rerank + dual-hypothesis sampler/fuser):

```bash
python3 tools/infra/dgx_spark_hybrid_orchestrator.py \
  --profile hermes-hybrid \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --skip-locked-build \
  --with-hypothesis-loop \
  --hyp-goal "construct nonstandard bridge theorem for modular transport closure" \
  --hyp-model-base qwen25-coder-7b-proposer \
  --hyp-model-tuned deepseek-prover-v2-7b-formalizer \
  --hyp-top-k 8 \
  --hyp-max-pass 2 \
  --hyp-emit-skills
```

If you already have candidate hypotheses and want only fuse+gate:

```bash
python3 tools/infra/dgx_spark_hybrid_orchestrator.py \
  --skip-locked-build \
  --skip-dataset \
  --skip-train \
  --skip-rerank \
  --with-hypothesis-loop \
  --skip-hypothesis-sampler \
  --hyp-input-candidates reports/training/hypothesis/candidates.jsonl \
  --hyp-goal "construct nonstandard bridge theorem for modular transport closure" \
  --hyp-top-k 8 \
  --hyp-max-pass 2
```

Low-memory backend profiles (for machines where Leanstral is too heavy):

```bash
set -a
source tools/infra/profiles/dgx_spark_lowmem_7b.env
set +a
bash tools/infra/deploy_spark_models.sh
```

If dual endpoints still OOM:

```bash
set -a
source tools/infra/profiles/dgx_spark_ultralow_single_7b.env
set +a
bash tools/infra/deploy_spark_models.sh
```

### Dual-Hypothesis Agent Lane

Sample hypotheses from two model roles (base + tuned):

```bash
python3 tools/infra/dual_hypothesis_sampler.py \
  --goal "construct nonstandard bridge theorem for modular transport closure" \
  --dag-context reports/training/arango_link_rerank.json \
  --base-url-base http://127.0.0.1:8000/v1 \
  --model-base qwen25-coder-7b-proposer \
  --base-url-tuned http://127.0.0.1:8000/v1 \
  --model-tuned deepseek-prover-v2-7b-formalizer \
  --samples-base 4 \
  --samples-tuned 4 \
  --out reports/training/hypothesis/candidates.jsonl
```

Fuse + Lean gate + optional generated skill emit:

```bash
python3 tools/infra/hypothesis_fuser_and_lean_gate.py \
  --input reports/training/hypothesis/candidates.jsonl \
  --goal "construct nonstandard bridge theorem for modular transport closure" \
  --top-k 8 \
  --max-pass 2 \
  --emit-skills \
  --out reports/training/hypothesis/fused-gated.json
```

## Generated DAG inputs

The DAG tools use generated declaration artifacts under
[artifacts/dag](../../artifacts/dag). Treat an artifact as current only when its
source revision, generation command, coverage, and freshness agree with the
checkout. Expected artifact names include:
- `full_graph.json`
- `index/decls.jsonl`
- `index/edges.jsonl`
- `index/edge-leakage.json`
- `index/morphisms.jsonl`
- `index/types.jsonl`
- `structural-topology.json`
- `source-sink-bipartite.json`
- `representation-depth-tags.json`
- `process-flow/` — Lean-authoritative exports: `flow-edges`, `process-events`, `lawful-path-candidates`, `defects`; Python-derived supplements: `flow-cocycles`, `comparison-candidates`

Derived readable outputs are written under `reports/dag/`. This is an output
location, not a guaranteed tracked directory in a fresh checkout.

## Maintained Refresh Order

After provisioning the configuration described above, the managed sequence
from [docs/ToolingMethodology.md](../../docs/ToolingMethodology.md) is:

```bash
lake script run dagAll
```

Execution-order rule:
- refresh must run before reports (`dagRefresh` -> `dagReports`), otherwise reports can legitimately reflect stale index inputs.
- for source deletes/renames, keep this order strict; do not run report generators directly on old artifacts.

Stale-source guard:
- `refresh_decl_graph.py` now refuses skip-mode when `artifacts/dag/index/decls.jsonl` references missing Lean source files.
- this closes the common contamination case where deleted files persisted through an incremental hash skip.

Expanded managed sequence:

```bash
lake script run dagStatus
lake script run dagRefresh
lake script run dagReports
lake script run dagDoctor
```

For active theorem/refactor work, prefer incremental owner builds between managed runs:

```bash
lake script run changedVerify --dry-run
lake script run changedVerify
```

This intentionally skips umbrella modules like `*.All` unless `--allow-umbrella` is passed.

Use the raw order below only when narrowing or repairing a tool failure.

Strict-coverage raw runbook (fails if graph coverage is partial):

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_hypothesis_debt_report.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/theorem_significance.py --out reports/theorem-significance-current.json --md reports/theorem-significance-current.md
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
python3 tools/infra/generate_replacement_frontier.py
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
python3 tools/infra/dag_status.py
python3 tools/infra/dag_doctor.py
```

Partial-coverage diagnostic variant (continues when coverage is known partial):

```bash
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json --allow-partial-coverage
python3 tools/infra/dag_status.py
python3 tools/infra/dag_doctor.py
```

Process-flow refresh (Lean export + Python derivation):

```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
python3 tools/infra/generate_semantic_flow_report.py
```

The Lean export writes the constitutive process-flow lane:
`flow-edges`, `process-events`, `lawful-path-candidates`, `defects`.
The Python step derives:
`flow-cocycles`, `comparison-candidates`, and the process-flow defect report.
This step can be heavy on large snapshots; run it after the core DAG reports are stable.
`generate_process_flow_report.py` now uses bounded comparison search by default
(`--max-comparison-pairs`, `--max-witness-searches`, `--max-comparison-seconds`)
to prevent superlinear blowups on large path sets.

`generate_semantic_flow_report.py` is the low-complexity semantic lane over
process-flow artifacts:
- signed chiral diffusion/relaxation (`O(iterations * E)`)
- pairwise entropy-production ranking (`O(E)`)
- SCC-level loop/holonomy obstruction proxies (`O(V + E)`)
It intentionally avoids full cycle enumeration and path-pair combinatorics.

Theory-cloud movie exporter (particle ontology over declarations):

```bash
python3 tools/infra/generate_theory_cloud_movie.py --mode semantic
python3 tools/infra/generate_theory_cloud_movie.py --mode structural
python3 tools/infra/generate_theory_cloud_movie.py --mode commits --commits WORKTREE,HEAD
```

`generate_theory_cloud_movie.py` treats declarations as particles and uses:
- structural attraction from declaration dependencies
- depth anchors from `structural-topology.json`
- semantic drift from process-flow-derived chiral/obstruction fields

Complexity is bounded for large snapshots by:
- node/edge caps (`--max-nodes`, `--max-edges`)
- local spatial hashing for repulsion (near-linear expected per step)
- fixed-step relaxation budget (`--steps`)

Commit mode reads artifacts via `git show`. If selected commits do not contain
the required DAG artifacts, the exporter skips them (or fails with
`--strict-commit-artifacts`).

For CI/lightweight enforcement, validate that the semantic lane executes and
emits the expected schema keys:

```bash
python3 tools/infra/check_semantic_flow_report.py
```

Explicit broad audit sequence (build + DAG + doctor + debt surfaces; use only
when this scope is intended, after configuration and dependencies are ready):

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --all-default-targets -- -R
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json --allow-partial-coverage --allow-uncovered-debt
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
python3 tools/infra/generate_replacement_frontier.py
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
python3 tools/infra/run_locked_lean.py --wait-for-build-lock --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
python3 tools/infra/dag_doctor.py
python3 tools/theorem_significance.py --out reports/theorem-significance-current.json --md reports/theorem-significance-current.md
python3 tools/infra/generate_hypothesis_debt_report.py --json-out reports/dag/hypothesis-debt-new-corpus.json --md-out reports/dag/hypothesis-debt-new-corpus.md
python3 tools/infra/reports/generate_vacuity_index.py --out reports/dag/hypothesis-vacuity-debt-current.md
python3 tools/infra/reports/generate_bridge_thinness_index.py
python3 tools/infra/reports/generate_surrogate_index.py
```

Interpretation notes:
- keep `canonical_policy_lint.py` as a hard signal; do not suppress failures in CI
- `dag_doctor.py` coverage-policy failure can coexist with fresh artifacts
- `generate_process_flow_report.py` is often the slowest step on large snapshots

Run the native audit before trusting the representation-depth reports. Run the main sequence sequentially. Do not trust `reports/dag/*` as current until the main sequence has finished.

## Operational Rules

- `run_locked_lake_build.py` with no positional target resolves the changed Lean
  owner modules incrementally. Use `--changed` for the explicit spelling; use
  `--all-default-targets` or a named umbrella only when a repository-wide gate
  is intentional.
- use `run_locked_lake_build.py --wait-for-build-lock` for explicit owner or
  umbrella builds, and `run_locked_lean.py --wait-for-build-lock` for individual
  Lean elaboration or `--run` script execution
- preserve `.lake`; do not clean the shared cache to solve a build failure
- follow the [root setup guide](../../README.md) for pinned local dependencies;
  the build wrapper checks workspace layout and attempts cache hydration before
  invoking Lake. The hydration subprocess uses `check=False`; its invocation
  does not guarantee success. Package-checkout validation is a separate step,
  and unavailable dependencies can prevent the subsequent Lake command from
  succeeding
- `refresh_decl_graph.py` now prebuilds `dagIndexer` for `--run-mode exe` and `DAG.Indexer` for `--run-mode run`, together with the import root, under the build lock
- do not run concurrent umbrella builds
- do not hand-edit `artifacts/dag/*`
- read code before acting on hotspot heuristics
- use the representation-depth reports as rendered summaries of the Lean-native grammar, not as the grammar itself
- use process-flow reports as local transport/coherence evidence, not as proof substitutes
- treat infra outputs as context-restoration tools: they should tell you what to read next, not what to believe without reading it

## Policy Surface

`canonical_policy_lint.py` enforces repository policy around:
- proposition-valued wrapper surfaces
- theorem-class tagging in canonical files
- suspect theorem burden in stable canonical owners
- reopening of structural hotspot and shell debt tracked by the refreshed artifacts

It is a source-level policy pass. Generated or internal declarations without a
valid source line are not part of its public-theorem scan.

## Build and audit evidence

See [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md) for recorded status
and [README.md](../../README.md) for the current entrypoint. A report date alone
does not establish the state of a later commit. Attach the source revision,
command, exit code, and relevant coverage/freshness information to a new audit.
This guide's source review did not run the managed refresh or certify a clean
repository-wide build.

- `external_refs/LeanMillenniumPrizeProblems/` mirror: searchable theorem corpus for the Clay problems.

- `graph_rag_query.py` (unified natural-language GraphRAG explorer over Lean, docs, black books, handover material, and external mirrors)
- `ask_repo.py` (thin user-facing wrapper for the GraphRAG explorer)
