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
- Lean files under `lean/`: `450`
- Lean LOC under `lean/`: `73,067`

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
- `tools/semantic_block_export.py`
  External Python LSP/RPC orchestrator for trusted semantic block export.
- `reports/dag/`
  Generated graph artifacts. These are intentionally untracked or regenerated.
- `tools/skynet_v2.py`
  Report-only semantic frontier explorer over trusted semantic block graphs.
- `tools/update_repo_docs.py`
  Refreshes tracked frontier/docs surfaces from the current trusted export set.

## Artifact Placement

Keep these graph layers distinct:
- `.build/full_graph.json` and `.build/index/decls.jsonl` are the trusted declaration-level inputs for causal-order analysis.
- `reports/dag/*.semantic-block.stdlib.json` are trusted semantic block exports for heavy modules.
- `reports/dag/true-root-order.{md,json}` are derived absolute causal-order reports built from the `.build/` graph artifacts plus the tracked audits.
- `reports/dag/openclaw-targets.{md,json}` are derived operational rankings built from `true-root-order.json`.

The mismatch that kept reappearing came from tool drift across two graph eras: older declaration-graph tooling assumed `full_graph.json` and `index/decls.jsonl` at repo root, while the current index/build workflow emits those trusted artifacts under `.build/`. A second drift then appeared when the causal report was updated to refresh markdown without refreshing its JSON sibling, leaving the target selector to read stale `true-root-order.json` state.

## Current vs Legacy

Use this split when entering the repository for the first time.

| Surface | Status | What to use it for |
| --- | --- | --- |
| `lean/InfoGeometry/Canonical`, `lean/InfoGeometry/KK`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Quantum` | Current | Main theorem library and publication surface |
| `lean/DAG`, `lean/scripts/DAG/Exploration` | Current | Graph extraction, semantic export, diagnostics, frontier analysis |
| `tools/semantic_block_export.py`, `tools/skynet_v2.py`, `tools/update_repo_docs.py` | Current | Trusted heavy-module export and auto-doc/frontier workflow |
| `docs/auto/index.md`, `lean/DAG/README.md`, `skills/info-geometry-repo/` | Current | Operational documentation and agent bootstrap |
| `archive/legacy/` | Archived but useful | Historical automation and scratch material worth mining for ideas, but not part of the supported build surface |
| `reports/dag/` | Generated / inspect after refresh | Analysis artifacts regenerated from the current code and export set |

The archive is intentionally kept in-tree for provenance and idea recovery. Start with current surfaces first, then consult [archive/README.md](/home/goutev/LEAN4/info-geometry-lean/archive/README.md) only if you are explicitly researching historical approaches.

## Build

Full project build:

```bash
lake build InfoGeometry.All
```

Canonical umbrella build:

```bash
lake build InfoGeometry.Canonical.All
```

Recursive rebuild:

```bash
lake build -R
```

DAG and semantic-export tooling:

```bash
lake build DAG semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
python3 -m py_compile tools/skynet_v2.py
```

## Semantic DAG Export

For large Mathlib-heavy modules, use the trusted stdlib server path:

```bash
python3 tools/semantic_block_export.py \
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

For advanced tooling details, read [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md).
The generated auto status page lives at [index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md).

## Frontier Discovery

The current frontier-discovery path is:

1. export trusted semantic block JSONs for heavy modules;
2. load them into `tools/skynet_v2.py`;
3. run diffusion from a named seed using `--walk forward|reverse|both`;
4. let Skynet apply debt-aware scheduling signals from the tracked audits;
5. generate report-only bridge candidates from the frontier packet;
6. use those candidate bridge statements as quarantine inputs, not proofs.

Example:

```bash
python3 tools/skynet_v2.py \
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
python3 tools/skynet_v2.py \
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
python3 tools/generate_auto_docs.py
```

To refresh the frontier packets and the tracked auto status page from the current trusted semantic export set:

```bash
python3 tools/update_repo_docs.py
```

To refresh semantic exports first, then rebuild the frontier from the full current export set:

```bash
python3 tools/update_repo_docs.py --refresh-exports
python3 tools/update_repo_docs.py --refresh-exports all
python3 tools/update_repo_docs.py --refresh-exports changed
```

`tools/update_repo_docs.py --refresh-exports ...` now degrades per-module semantic-export failures on thin façade modules to warnings, keeps any existing export artifact, and continues. Treat those warnings as tooling noise to inspect, not as proof that the whole graph refresh failed.

This refresh also regenerates the tracked bridge-candidate packet from the current trusted frontier and audit state.

## How To Read The Theory Topology

There are three useful views:

1. declaration DAG
- best for SCCs, dominators, and global bottlenecks

2. block export
- best for source attribution and minimal slices

3. semantic block graph
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
4. build `InfoGeometry.All`
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
