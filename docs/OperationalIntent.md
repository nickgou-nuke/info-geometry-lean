# Operational Intent

This repository is one theory with several representation levels.
The main formal burden is to make the morphisms between those levels explicit, adjacent, and checkable.

## What Is Being Formalized

The stable spine is a semantic representation ladder defined by the
`RepDepth` inductive in `lean/InfoGeometry/Meta/Architecture.lean`
and enforced at build time via `@[rep_depth]` attributes and
`#audit_architecture` (run in `lean/InfoGeometry/Audit.lean`).

| `RepDepth` | Semantic domain | Example owners |
|---|---|---|
| `count` | relative-volume data | `PositiveRayCore` |
| `projective` | gauge / relative-potential data | `RelativePotentialCore` |
| `operator` | partition / modular-lift data | `RelativeSurprisalOperatorLift` |
| `krein` | Clifford / polarized-sheet data | `KreinDiracSpectralLift` |
| `transport` | Bogoliubov / spectral-change data | `BogoliubovPolarizationBridge` |
| `thermo` | attention / Gibbs-Sinkhorn data | `AttentionPolarizedGibbsBridge` |

The important mathematical content is not only the objects at each layer.
It is the enforced morphisms between them:
- owner definitions at the lowest natural level
- adjacent translators between neighboring levels
- coherence theorems proving that rival adjacent composites agree
- capstones that summarize lower content without pretending to be foundational owners

## Current Proven Corridor

The current clean example of that policy is the representative-to-operator relative-potential chain:
- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean) owns positive representatives and normalization mass
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean) performs the quotient-level gauge descent
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean) owns the canonical unary ray language (`@[rep_depth count]`)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean) now owns `representativeMassShift` and its cocycle (`@[rep_depth projective]`)
- [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean) specializes that cocycle to `countMassShift` (`@[rep_depth count]`)
- [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean) lifts it to the operator and averaged modular-Hamiltonian branch (`@[rep_depth operator]`)

The corridor endpoint is now explicit: `relativeModularHamiltonian_sub_countMassShift_cocycle` proves that the operator branch consumes the owned normalization cocycle rather than recomputing local log-mass algebra.

## What Canonical Means

`canonical` means the stable public owner surface.
It does not mean the only valid mathematics in the repository.

Valid but unfinished mathematics should be:
- developed on noncanonical or exploratory surfaces
- quarantined honestly when it is not yet stable
- promoted when the owner-level proofs become real

What should be removed are theorem-shaped wrappers and facade surfaces that do not carry mathematical load.

## Why DAG And Python Tooling Exist

The DAG and infra layers were developed to preserve operational memory and make the repository readable after context loss.
They serve four jobs:

1. externalize dependency memory from the Lean environment into stable artifacts
2. expose owner / translator / coherence / capstone pressure on the declaration graph
3. surface theorem-wrapper burden, representation-depth legality, and residual comparison debt
4. give CI and humans a reproducible view of the current structural state

Recent improvements:
- **Unified graph construction**: a single typed adjacency map is built once; `full_graph.json` is projected from it
- **Artifact metadata**: `artifacts/dag/index/meta.json` records `schemaVersion` (≥ 2), ISO timestamp, node/edge/morphism/type counts, and `oleanHash`
- **Edge validation**: `validateEdges` enforces referential integrity at export time
- **Atomic writes**: `atomicWriteFile` prevents partial artifact corruption
- **Incremental refresh**: `refresh_decl_graph.py` skips when the olean content hash matches the previous run; use `--force` to override

They do **not**:
- define mathematical truth
- replace direct code reading
- invent ontology that is absent from Lean
- justify deleting valid mathematics by heuristic alone

## The Declaration Graph As A Mathematical Object

The compiled Lean corpus is not only metadata about the theory.
Once exported, the declaration graph is itself a finite, explicit, kernel-grounded mathematical object.

That matters because the repository now exposes, on the graph side:
- a finite chain-complex-like incidence structure
- real boundary and coboundary operators
- real Laplacians and spectral invariants
- real notions of cycles, roots, shells, and flow defects

This is productive self-reference, not empty circularity.
The first object is the checked theory inside the Lean kernel.
The second object is the finite structural shadow produced by compiling that checked theory into declarations, dependencies, SCCs, process-flow events, and incidence artifacts.

That second object can reveal structural facts about the presentation of the theory that file-by-file reading cannot recover globally:
- whether a bridge is genuinely load-bearing
- whether a region is root-supported or facade-supported
- where coherence pressure accumulates
- where causal shells are thin or broken
- where transport corridors have spectral bottlenecks

The discipline is strict:
- never let graph invariants replace Lean source as the truth surface
- do let graph invariants expose global structure that direct local reading cannot see on its own

This is why `true-root-order`, the replacement frontier, and the process-flow artifacts are useful when they remain subordinate to Lean source rather than being treated as oracles.

## Tooling Contract

The trusted order is:
1. Lean source
2. Lean-native audit
3. `artifacts/dag/index/meta.json` — schema gate and freshness check (`schemaVersion` ≥ 2, recent `timestamp`)
4. atomic DAG artifacts (`full_graph.json`, `index/*.jsonl`, `structural-topology.json`)
5. derived Python reports
6. prose

The DAG layer is maintained because raw code reading alone does not scale once the theory spreads across many representation surfaces.
The Python layer is maintained because regenerated reports are the fastest way to recover context, localize debt, and choose the next honest file to inspect.
Before trusting any artifact, check `meta.json` for timestamp and schema version.

## Process-Flow Layer

The newer process-flow tooling is specifically for constitutive transport evidence.

Lean side:
- [ProcessFlowExport.lean](../lean/DAG/ProcessFlowExport.lean)

Python side:
- [generate_process_flow_report.py](../tools/infra/generate_process_flow_report.py)

This layer exists to make local flow evidence explicit:
- `FlowEdge` as the primitive carrier
- `ProcessEvent` as edge aggregation
- bounded path candidates as secondary derived objects
- localized defect rows
- derived comparison and cocycle reports downstream

Its purpose is to audit transport and coherence pressure, not to replace theorem proofs.

## Default Reading Order

When context has been purged, rebuild intention in this order:
1. [README.md](../README.md)
2. [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
3. [docs/Theory.md](Theory.md)
4. [lean/DAG/README.md](../lean/DAG/README.md)
5. [tools/infra/README.md](../tools/infra/README.md)
6. the specific owner files and regenerated reports relevant to the task
