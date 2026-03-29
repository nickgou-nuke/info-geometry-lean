# One Theory, Many Presentations

This repository is best read as a stratified tower of presentations of one underlying theory.
The important mathematical content is not only in the objects at each layer, but in the coherence theorems proving that different adjacent translation paths agree.
Those adjacent morphisms are the main formal target.
The repository should not be flattened into one facade surface; it should make the representation changes explicit and check that they commute.

The representation grammar is now partially enforced natively inside Lean:
- [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean) defines depth metadata and the dependency-span audit
- [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean) is the CI entrypoint

Python reports remain useful, but they are downstream views over a grammar that Lean itself now checks.

## Representation Depth

| Layer | Presentation | Typical owners |
| --- | --- | --- |
| `L0` | Count / relative-volume data | `RelativePotentialCountBridge` |
| `L1` | Projective / gauge / relative potential | `PositiveRayCore`, `RelativePotentialCore`, `RedLine` |
| `L2` | Operator / modular lift | `InformationPartitionCore`, `RelativeSurprisalOperatorLift` |
| `L3` | Krein / Clifford geometry | `SplitQuadratic`, `SplitQuadraticSheets`, `PolarizedSector` |
| `L4` | Transport / Bogoliubov frame change | `KreinDiracSpectralLift`, `SplitCliffordThermalBridge` |
| `L5` | Thermodynamic / attention surfaces | `AttentionPolarizedSplit`, `AttentionPolarizedGibbsBridge`, `AttentionPolarizedSinkhornBridge` |

## Current Anchor Corridor

The deepest currently stabilized count-to-operator corridor is:
- [PositiveMeasure.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [RelativePotentialCountBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- [RelativeSurprisalOperatorLift.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

Its new owner/cocycle seam is:
- `representativeMassShift` and `representativeMassShift_cocycle` at the representative level
- `countMassShift` and `countMassShift_cocycle` at the count specialization level
- `relativeCountModularPotentialOperator_cocycle` at the raw diagonal-operator level
- `relativeModularHamiltonian_sub_countMassShift_cocycle` at the averaged operator level

This is the current benchmark for what a nonvacuous adjacent corridor should look like in the repository.

## File Roles

Every stable file should be read as one of four roles:
- owner: defines the lowest natural surface for a presentation
- translator: moves one adjacent depth step
- coherence: proves that two adjacent composites agree
- capstone: consumes lower layers without defining new skip-level ontology

This role split is not just documentation style.
It is the repo's way of preserving one theory across several symmetric, operator, Krein, transport, and thermodynamic realizations without pretending they are the same file-level object.

The anti-facade rule is simple:
- a valid bridge file is either an adjacent translator or a real coherence file
- direct skip-level ontology is debt

In Lean-native terms, the current V1 rule is:
- a tagged non-capstone declaration at depth `d` may only reach tagged declarations at depth `d` or `d - 1`
- a theorem that spans further must be explicitly treated as capstone/composite surface

## What Is Actually Proved

The stable spine currently includes real seams such as:
- count to projective/gauge translation in [RelativePotentialCountBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- operator lift in [RelativeSurprisalOperatorLift.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)
- diagonal spectral-to-modular bridge in [DiagonalMetricModularBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean)
- attention equals Gibbs weights in [AttentionPolarizedGibbsBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean)
- Sinkhorn and matrix-side transport in [AttentionPolarizedSinkhornBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean)

The repo does not treat grand rhetoric as proof. A capstone claim is only live when it is built from owner-level lower theorems already present in the codebase.

## Live Structural Artifacts

The stable bicategorical map is exposed by:
- [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)
- [representation-depth-audit.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/representation-depth-audit.md)
- [representation-depth-graph.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/representation-depth-graph.md)
- [true-root-order.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/true-root-order.md)
- [theorem-surface-index.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/theorem-surface-index.md)

Read the reports as derived views over Lean source, the native audit, and the declaration DAG, not as replacements for them.
Their job is to restore context quickly and localize pressure; their job is not to replace owner-file reading.

## What Remains Open

The current remaining debt is mostly not proof gaps in the stable path.
It is:
- representation debt in review-surface files still leaning on quarantined ontology
- theorem-surface debt in some bridge files with heavy public surfaces
- visualization debt, especially replacing hotspot-based coloring with a depth-aware projector

The cleaned spine should be treated as a stable substrate for those next passes.
