# InfoGeometry in Lean 4

This repository has two tightly coupled layers:

1. a Lean 4 theory library for information geometry, gauge transport, operator/K-theoretic structure, modular/CPT bridges, discrete phase scaffolds, and synthesis modules;
2. a semantic DAG engine that extracts declaration-level and source-block-level theory topology from Lean while filtering elaborator noise for heavy modules.

It is therefore both a theorem repository and a structural analysis environment for the theory itself.

## Axiomatic Goal

The standing goal of the repository is:

> identify the true axiomatic base of the theory, then build upward lemma by lemma and theorem by theorem from that base.

That base is not a single declaration. It is a root set.

The current intended order of primitiveness is:

1. unnormalized count, ray, and Radon-Nikodym structure
- relative count density, relative volume change, modular/RN data, and the measure-theoretic substrate below normalized probability language
2. graded real operator geometry
- `KreinGradedModule`, real Krein carriers, endomorphism language, and the internal split-Clifford atom
3. internal square-minus-one axis
- `K := J.comp eps`, with external scalar `complex_i` treated as legacy-only naming, not primitive data
4. derived normalized information geometry
- entropy, KL, Jaynes, IB, gauge transport, analytical index, modular anomaly, and synthesis layers

Normalized probabilities are therefore not the deepest floor here. Unnormalized counts, rays, and RN derivatives sit lower in the semantic stack.

## Hard Proof Policy

This repository does not count vacuous acceptance by Lean as mathematical closure.

- `sorry`, `admit`, `axiom`, and placeholder contract surfaces are banned from the stable theorem story.
- A theorem that is only `trivial`, direct assumption unpacking, alias transport, or definitional repackaging does not count as frontier progress.
- Real progress means: start from existing concrete data already present in the repo, construct the needed witness or bridge in Lean, and prove a nonvacuous relation, invariance, obstruction, or existence result.
- Assumption-driven wrappers, API façades, and packaging theorems are allowed only when labeled honestly as packaging, not presented as completed unification.
- The absence of `sorry` is necessary but not sufficient; the result must also be constructive and nonvacuous.

If you are new to the repository, start with [NEWCOMER_PATH.md](/home/goutev/LEAN4/info-geometry-lean/NEWCOMER_PATH.md) before diving into the full DAG/tooling stack.
If you want the semantic top view of the theory, read [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md).
If you want the deeper count / ray / RN / gauge substrate, also read [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md).
If you want the shortest exact path through the Universal Volume / RN stack, read [UNIVERSAL_VOLUME_STACK.md](/home/goutev/LEAN4/info-geometry-lean/UNIVERSAL_VOLUME_STACK.md).
If you want the current trust/debt boundary for assumptions, wrappers, and surrogate surfaces, read [SURROGATE_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/SURROGATE_INDEX.md).
If you want the current alias/vacuity debt boundary, read [VACUITY_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/VACUITY_INDEX.md).
If you want the current thin-bridge audit for definitional identities and direct-forward bridge surfaces, read [BRIDGE_THINNESS_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/BRIDGE_THINNESS_INDEX.md).
If you want the current theorem-to-literature and module-level unification audit, read [UNIFICATION_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/UNIFICATION_INDEX.md).
If you want the current dual-lane creative/critical LLM workflow for frontier packets, read [LLM_FRONTIER_PROTOCOL.md](/home/goutev/LEAN4/info-geometry-lean/LLM_FRONTIER_PROTOCOL.md).
If you want the current dual-lane creative/critical LLM workflow for constructive debt replacement, read [LLM_DEBT_PROTOCOL.md](/home/goutev/LEAN4/info-geometry-lean/LLM_DEBT_PROTOCOL.md).
If you want the current manually reviewed quarantine-ready bridge packet for concrete frontier runs, read [bridge-reviewed-candidates.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/bridge-reviewed-candidates.md).

## Verified Shape

Current repository scale:
- Lean files under `lean/`: `475`
- Lean LOC under `lean/`: `81,755`

Current synchronized structural stories:
- primitive real split-Krein spine:
  `InfoGeometry.Krein.KreinGradedModule`
  -> `InfoGeometry.Quantum.RealSplitClifford.RealSplitCl11Action`
  -> `InfoGeometry.KK.RealSplitKreinKasparovCycle`
  -> `InfoGeometry.KK.RealSplitKreinUnboundedCycle`
- KK / analytical-index / synthesis:
  `InfoGeometry.KK.KasparovCycle.analyticalIndex`
  -> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
  -> `InfoGeometry.Canonical.GrandSynthesis.*`
- source-tension / Rosetta / modular anomaly:
  `Singular`, `RicciMongeAmpere`, `BogoliubovFockSuper`, `TomitaTakesaki`
  -> `InfoGeometry.Canonical.Rosetta.*`
  -> `InfoGeometry.Quantum.ModularAnomaly.*`
- Weyl-scale transport into KK and Jordan/KKT:
  `WeylTransport`, `WeylInformationGauge`
  -> `Rosetta.weylScaleTransportShadow_to_modularCliffordTransport`
  -> `Rosetta.kk_analyticalIndex_eq_of_weylScaleTransport`
  and `Rosetta.weylScaleTransportScalarShadow_generalized_pythagorean_of_jordanBregman`
- discrete Hurwitz shell into RG stationarity:
  `InfoGeometry.Quantum.Hurwitz`
  -> `InfoGeometry.Quantum.HurwitzRGFlow`
  -> `InfoGeometry.Canonical.RGFlow`
- finite Pfaffian-sign phase boundary:
  `InfoGeometry.Quantum.KitaevChain.index_change_forces_defect_crossing`
- deeper count / RN / gauge substrate:
  `relativeCountDensity`, `relativeVolumeChangeRN`, `relativeTomitaTakesakiOp`
  -> `WeylGaugeField`, `WeylTransport`, `YangMillsContinuum`
  -> synthesis surfaces

Tracked trusted semantic exports exist for heavy capstones such as:
- `GrandSynthesis`
- `AnalyticalIndex`
- `KasparovCycle`
- `CayleyBregmanBridge`
- `BogoliubovFockSuper`

The exact frontier graph counts are intentionally not duplicated here. Use the tracked status page at [index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md) and the current packets under `reports/dag/` for live numbers after refresh.

## Repository Map

### Domain layer

- `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
  Generator / flow / response spine.
- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
  Local Weyl-gauge layer.
- `lean/InfoGeometry/Canonical/WeylTransport.lean`
  Heavy transport/integration layer.
- `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
  Primitive real split `Cl(1,1)` atom.
- `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
  Primitive bounded real split-Krein Fredholm-like cycle.
- `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean`
  Primitive domain-based unbounded split-Krein scaffold.
- `lean/InfoGeometry/KK/KasparovCycle.lean`
  Legacy-compatible KK façade above the new primitive split-Krein layer.
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
  Large chiral/index-invariance web.
- `lean/InfoGeometry/Canonical/Rosetta.lean`
  Assumption-driven capstone transport façade linking source tension, Weyl transport, KK invariance, Jordan/KKT geometry, and modular anomaly presentations.
- `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
  Real-Majorana modular cocycle shadow plus finite lattice anomaly / determinant / Berezinian layer.
- `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
  Discrete 24-chart Hurwitz shell bridge into RG stationarity.
- `lean/InfoGeometry/Quantum/KitaevChain.lean`
  Finite Pfaffian-sign chain scaffold with critical/defect crossing theorems.
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
  Large synthesis layer.

### Tooling layer

- `lean/DAG/`
  Importable graph/topology engine.
- `lean/scripts/DAG/Exploration/`
  Lean report generators and entrypoints.
- `tools/frontier/semantic_block_export.py`
  External Python LSP/RPC orchestrator for trusted semantic block export.
- `reports/dag/`
  Generated graph artifacts. These are intentionally untracked or regenerated.
- `tools/frontier/skynet_v2.py`
  Report-only semantic frontier explorer over trusted semantic block graphs.
- `tools/docs/update_repo_docs.py`
  Refreshes tracked frontier/docs surfaces from the current trusted export set.

## Artifact Placement

Keep these graph layers distinct:
- `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl` are the public authoritative atomic declaration-DAG inputs for causal-order analysis.
- `artifacts/dag/structural-topology.json` is the public authoritative native structural-analysis layer emitted by Lean: stable condensation-node ids, component membership, condensation edges, layer data, dominator summaries, and canonical root-witness paths.
- `artifacts/dag/source-sink-bipartite.json` is the public authoritative correspondence object between atomic declaration truth and hydrated readable carriers.
- `reports/dag/true-root-order.{md,json}`, `reports/dag/openclaw-targets.{md,json}`, `reports/dag/source-sink-compression.{md,json}`, and the GraphML / SVG views under `reports/dag/` are derived readable reports built from the authoritative `artifacts/dag/` layer plus the tracked audits.
- `reports/dag/*.semantic-block.stdlib.json` are trusted semantic block exports for heavy modules and stay separate from the declaration-DAG / correspondence lane.

The mismatch that kept reappearing came from tool drift across two graph eras: older declaration-graph tooling assumed `full_graph.json` and `index/decls.jsonl` at repo root, while a later generation pushed the trusted declaration export into the hidden `.build/` cache. The current repository policy is to keep the authoritative atomic DAG, native structural topology, and public correspondence layer in `artifacts/dag/`, with `.build/` treated only as a transient build cache or explicit compatibility fallback. A second drift then appeared when readable markdown/JSON reports were refreshed without refreshing their authoritative inputs, leaving downstream selectors and graph summaries to read stale state.

## Tooling Hierarchy

Read the operational documentation in this order:

1. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
- repository-wide proof policy, artifact placement, and current-vs-legacy split

2. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
- Lean-side graph engine and export-lane hierarchy

3. [tools/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/README.md)
- Python orchestration hierarchy and script status

The hierarchy of trust is:

1. authoritative declaration DAG, native structure, and correspondence lane
- [refresh_decl_graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/refresh_decl_graph.py) -> [Indexer.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/Indexer.lean) -> `artifacts/dag/full_graph.json`, `artifacts/dag/index/decls.jsonl`, and `artifacts/dag/structural-topology.json`
- [generate_source_sink_compression.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_source_sink_compression.py) -> `artifacts/dag/source-sink-bipartite.json`
- consumed by [generate_causal_report.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_causal_report.py), [select_openclaw_target.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/select_openclaw_target.py), [classify_missing_all.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/classify_missing_all.py), [generate_theorem_surface_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_theorem_surface_index.py), [plot_decl_graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/plot_decl_graph.py), [generate_structural_dedup.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_structural_dedup.py), [generate_structural_fibers.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_structural_fibers.py), and the readable `reports/dag/*` projections

2. authoritative blueprint / LeanArchitect lane
- [refresh_blueprint_tags.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/refresh_blueprint_tags.py) -> [auto_blueprints.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/auto_blueprints.lean) and [BlueprintTags.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/BlueprintTags.lean)
- consumed by `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags`, `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint`, and `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprintJson`
- human-facing narrative lives under [blueprint/README.md](/home/goutev/LEAN4/info-geometry-lean/blueprint/README.md) and `blueprint/src/generated/content.tex`

3. authoritative semantic-block lane
- [semantic_block_export.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/semantic_block_export.py) -> `reports/dag/*.semantic-block.stdlib.json`
- consumed by [skynet_v2.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/skynet_v2.py), [generate_auto_docs.py](/home/goutev/LEAN4/info-geometry-lean/tools/docs/generate_auto_docs.py), and [update_repo_docs.py](/home/goutev/LEAN4/info-geometry-lean/tools/docs/update_repo_docs.py)

4. limited native auxiliary lane
- [RootOrderExport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/RootOrderExport.lean) and similar native reports are useful, but they are not the default current refresh path

5. compatibility / legacy lane
- [ExportForwardGraph.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/ExportForwardGraph.lean)
- [ExportDecls.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/ExportDecls.lean)
- [graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/graph.py)
- `docs-map/graph.json`
- archived module-graph helpers under [archive/legacy/](/home/goutev/LEAN4/info-geometry-lean/archive/legacy/README.md)

These compatibility surfaces are archived for archaeology only and are not part of the canonical causal-order workflow.

## Current vs Legacy

Use this split when entering the repository for the first time.

| Surface | Status | What to use it for |
| `lean/InfoGeometry/Canonical`, `lean/InfoGeometry/KK`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Quantum` | Current | Main theorem library and publication surface |
| `tools/infra/refresh_decl_graph.py` + `lean/DAG/Indexer.lean` + `artifacts/dag/full_graph.json` + `artifacts/dag/index/decls.jsonl` | Current / authoritative | Atomic declaration-level causal order, coverage, and rooted partial-order analysis |
| `tools/infra/refresh_decl_graph.py` + `lean/DAG/StructuralExport.lean` + `artifacts/dag/structural-topology.json` | Current / authoritative | Native condensed structural topology with stable component ids, membership, condensation edges, layer data, dominator summaries, and canonical root-witness paths |
| `tools/infra/generate_source_sink_compression.py` + `artifacts/dag/source-sink-bipartite.json` | Current / authoritative | Stable correspondence layer between atomic declaration truth and hydrated readable carriers; source bundles, motif signatures, witness counts, and compression carriers |
| `tools/infra/generate_causal_report.py`, `tools/infra/select_openclaw_target.py`, `tools/infra/classify_missing_all.py`, `tools/infra/generate_theorem_surface_index.py`, `tools/infra/plot_decl_graph.py`, `tools/infra/generate_structural_dedup.py`, `tools/infra/generate_structural_fibers.py` | Current / authoritative | Readable causal reports, operational rankings, theorem-surface classification, quotient/fiber diagnostics over the source-sink correspondence layer, and full/tracked-frontier NetworkX graph exports |
| `tools/infra/refresh_blueprint_tags.py`, `lean/InfoGeometry/auto_blueprints.lean`, `lean/InfoGeometry/BlueprintTags.lean`, LeanArchitect `:blueprint` / `:blueprintJson` facets | Current / authoritative | Blueprint coverage refresh and exact theorem-to-TeX/JSON extraction |
| `tools/frontier/semantic_block_export.py`, `tools/frontier/skynet_v2.py`, `tools/docs/update_repo_docs.py` | Current / authoritative | Trusted heavy-module export and frontier workflow |
| `lean/DAG/RootOrderExport.lean`, `lean/DAG/SkeletonExport.lean`, `lean/scripts/DAG/Exploration/*` | Current / auxiliary | Native reports and diagnostics that sit beside, not above, the authoritative `artifacts/dag` pipeline |
| `lean/DAG/ExportForwardGraph.lean`, `lean/DAG/ExportDecls.lean` | Compatibility / limited | Older declaration export paths kept only for auxiliary inspection beside the authoritative `artifacts/dag` lane |
| `tools/graph.py`, `docs-map/graph.json`, `archive/legacy/scripts/make_graph.py` | Legacy / compatibility | Older module-graph consumer lane; archived and not part of canonical causal-order truth |
| `archive/legacy/` | Archived but useful | Historical automation and scratch material worth mining for ideas, but not part of the supported build surface |
| `reports/dag/` | Generated / inspect after refresh | Analysis artifacts regenerated from the current code and export set |


The archive is intentionally kept in-tree for provenance and idea recovery. Start with current surfaces first, then consult [archive/README.md](/home/goutev/LEAN4/info-geometry-lean/archive/README.md) only if you are explicitly researching historical approaches.

## Build

Full project build:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

Canonical umbrella build:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

Recursive rebuild:

```bash
python3 tools/infra/run_locked_lake_build.py -R
```

Single-build rule:
- do not launch multiple full or umbrella builds concurrently
- use `python3 tools/infra/run_locked_lake_build.py ...` so a second build fails fast on the shared build lock

DAG and semantic-export tooling:

```bash
lake build DAG semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
python3 -m py_compile tools/frontier/skynet_v2.py
```

## Semantic DAG Export

For large Mathlib-heavy modules, use the trusted stdlib server path:

```bash
python3 tools/frontier/semantic_block_export.py \
  lean/InfoGeometry/Canonical/GrandSynthesis.lean \
  reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900 \
  --transcript reports/dag/GrandSynthesis.semantic-block.stdlib.transcript.jsonl \
  --stderr-log reports/dag/GrandSynthesis.semantic-block.stdlib.stderr.log
```

Why this path matters:
- it uses a separate `lean --server` process;
- it avoids host/guest `[init]` collisions on heavy files;
- it produces semantic block graphs filtered to `primaryProduces`, while preserving `auxProduces` in the causal substrate.

For advanced Lean-side graph details, read [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md).
For Python-side orchestration status, read [tools/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/README.md).
The generated auto status page lives at [index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md).

## Frontier Discovery

The current frontier-discovery path is:

1. export trusted semantic block JSONs for heavy modules;
2. load them into `tools/frontier/skynet_v2.py`;
3. run diffusion from a named seed using `--walk forward|reverse|both`;
4. let Skynet apply debt-aware scheduling signals from the tracked audits;
5. generate report-only bridge candidates from the frontier packet;
6. use those candidate bridge statements as quarantine inputs, not proofs.

Example:

```bash
python3 tools/frontier/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk reverse \
  --top 12 \
  --json-out reports/dag/skynet-v2-frontier-reverse.json \
  --md-out reports/dag/skynet-v2-frontier-reverse.md
```

Example mixed-seed true-category packet around the current primitive split-Krein and index spine:

```bash
python3 tools/frontier/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/RealSplitClifford.semantic-block.stdlib.json \
  --input reports/dag/RealSplitKreinKasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/RealSplitKreinUnboundedCycle.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --seed RealSplitCl11Action \
  --seed RealSplitKreinKasparovCycle \
  --seed RealSplitKreinUnboundedCycle \
  --walk both \
  --top 21 \
  --json-out reports/dag/skynet-v2-frontier-true-category.json \
  --md-out reports/dag/skynet-v2-frontier-true-category.md
```

Operational rules:
- `forward` shows dependencies/bases;
- `reverse` shows downstream consumers;
- `both` shows the local bridge kernel around the seed set;
- seed distance is not absolute theory depth.

True DAG depth must be measured from the exported graph's dependency root set, not from the chosen Skynet seeds. A DAG usually has many primitive roots, not one common root.

To regenerate the tracked auto status page from current local artifacts:

```bash
python3 tools/docs/generate_auto_docs.py
```

To refresh the frontier packets and the tracked auto status page from the current trusted semantic export set:

```bash
python3 tools/docs/update_repo_docs.py
```

To refresh semantic exports first, then rebuild the frontier from the full current export set:

```bash
python3 tools/docs/update_repo_docs.py --refresh-exports
python3 tools/docs/update_repo_docs.py --refresh-exports all
python3 tools/docs/update_repo_docs.py --refresh-exports changed
```

`tools/docs/update_repo_docs.py --refresh-exports ...` now degrades per-module semantic-export failures on thin façade modules to warnings, keeps any existing export artifact, and continues. Treat those warnings as tooling noise to inspect, not as proof that the whole graph refresh failed.

This refresh also regenerates the tracked bridge-candidate packet from the current trusted frontier and audit state.

## How To Read The Theory Topology

There are four useful views:

1. declaration DAG
- best for SCCs, dominators, and global bottlenecks

2. source-sink bipartite correspondence artifact
- best for source bundles, repeated path motifs, canonical witness paths, and projection from atomic theorem packets into hydrated carriers

3. block export
- best for source attribution and minimal slices

4. semantic block graph
- best for human-facing theory structure and bridge hunting

Current topology picture:
- the repository should be read as a DAG with a root set, not as a single-spine tree;
- absolute depth from true dependency roots and distance from a chosen seed set are different metrics;
- the deepest visible floors include unnormalized count/ray/RN structure, `KreinGradedModule`, the real split `Cl(1,1)` atom, and the operator carrier language on real Krein spaces;
- the KK / analytical-index corridor remains the cleanest classical-style vertical trunk;
- the primitive real split-Krein KK spine is now explicit and separate from the legacy KK façade;
- `Canonical.Rosetta` exposes the current source-tension transport façade joining singular, Weyl, KK, Jordan/KKT, and modular surfaces;
- `Quantum.ModularAnomaly` and `Quantum.KitaevChain` provide finite quantum/topological shadow layers;
- `Quantum.HurwitzRGFlow` is the checked discrete-shell bridge into RG stationarity.

## Agent Bootstrap

If you are using a coding agent, the minimal bootstrap sequence is:

1. read [docs/keyword_index.md](/home/goutev/LEAN4/info-geometry-lean/docs/keyword_index.md)
2. read [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
3. read [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
4. run `python3 tools/infra/run_locked_lake_build.py InfoGeometry.All`
5. decide whether the task is:
   primitive/root-set work,
   KK/index work,
   count/RN/gauge work,
   modular/Rosetta work,
   discrete phase/RG work,
   global topology,
   semantic export,
   or frontier analysis

There is also a repo-specific agent skill in `skills/info-geometry-repo/`.
For bridge work, the most relevant references are:
- `skills/info-geometry-repo/references/frontier-prompt.md`
- `skills/info-geometry-repo/references/bridge-candidates.md`

For historical context or discarded automation ideas, see [archive/README.md](/home/goutev/LEAN4/info-geometry-lean/archive/README.md).

## Release Integrity

The intended alpha-release policy is:
- keep the full `.git` history;
- exclude build garbage and generated DAG artifacts from the release archive;
- publish a source archive with checksum and signature;
- keep theorem source, DAG tooling, and orchestration scripts together as one reproducible unit.
