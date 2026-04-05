# Module Map

This page is a first-pass navigation aid for the repository.
For maintained-vs-reference doc status, start with
[`RepositoryMemoryMap.md`](RepositoryMemoryMap.md).
For live truth, trust Lean source first, then
[`Audit.lean`](../lean/InfoGeometry/Audit.lean), then `artifacts/dag/`,
then `reports/dag/`.

## Entry Surfaces

These files are easy to confuse on a first read. Their roles are different.

| File | Use it when | Do not start here if |
|------|-------------|----------------------|
| [`InfoGeometry.lean`](../lean/InfoGeometry.lean) | you want the published Lean library entrypoint | you need the whole project graph or experimental layers |
| [`Library.lean`](../lean/InfoGeometry/Library.lean) | you want the stable, linted canonical publication surface | you need to inspect quarantine boundaries or noncanonical modules |
| [`Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean) | you are working inside the stable canonical owner/translator/coherence surface | you need the repo-wide graph, not just the stable publication umbrella |
| [`All.lean`](../lean/InfoGeometry/All.lean) | you need the full project umbrella, including canonical, exploratory, and bedrock layers | you only need the stable public surface |
| [`Audit.lean`](../lean/InfoGeometry/Audit.lean) | you want the Lean-native architecture check surface used by CI and infra | you are looking for mathematical owners rather than policy enforcement |
| [`Architecture.lean`](../lean/InfoGeometry/Meta/Architecture.lean) | you need to understand `@[rep_depth]`, `@[capstone]`, and adjacency enforcement | you are looking for a guided overview of the theory itself |

## Major Module Families

Read the repo by family, not as one flat directory listing.

Current Structural Status:
- **Active target**: `InfoGeometry.Canonical.AnalyticalIndexCoupled` (shell-heavy, 5 suspect surfaces)
- **Reduced debt**: `InfoGeometry.Canonical.CalabiYauMetricRicci` (residual math burden remains, but wrapper debt is cleared)

| Area | What lives there | Good first file |
|------|------------------|-----------------|
| `PositiveMeasure.lean`, `Measure/`, `Volume/` | positive representatives, mass, RN/log-volume, and related foundational measure surfaces | [`PositiveMeasure.lean`](../lean/InfoGeometry/PositiveMeasure.lean) |
| `Projective/`, `MeasureProjective/` | quotienting by positive rescaling, normalization gauges, and projective descent | [`Projective/Normalize.lean`](../lean/InfoGeometry/Projective/Normalize.lean) |
| `Canonical/` | the stable owner/translator/coherence public surface; this is the main maintained publication umbrella | [`Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean) |
| `Core/`, `Architecture/`, `Convex/` | shared geometric, algebraic, and structural substrate used across multiple presentations | [`Core/All.lean`](../lean/InfoGeometry/Core/All.lean) |
| `ExponentialFamily/`, `MaxEnt/`, `Thermo/` | statistical mechanics, inference, entropy, Gibbs, and thermodynamic layers | [`MaxEnt/All.lean`](../lean/InfoGeometry/MaxEnt/All.lean) |
| `Krein/`, `Clifford/`, `Jordan/`, `KK/` | split quadratic, Clifford, Jordan, and operator-algebra side presentations | [`Krein/All.lean`](../lean/InfoGeometry/Krein/All.lean) |
| `Quantum/`, `Prequantum/` | quantum and transport-facing extensions and bridges | [`Quantum/All.lean`](../lean/InfoGeometry/Quantum/All.lean) |
| `Meta/`, `Lint/` | architecture grammar, vacuity checks, and repo policy hooks | [`Architecture.lean`](../lean/InfoGeometry/Meta/Architecture.lean) |
| [`lean/DAG/`](../lean/DAG/README.md), [`tools/infra/`](../tools/infra/README.md) | the graph export, process-flow, reporting, and orchestration layers | [`lean/DAG/README.md`](../lean/DAG/README.md) |

## Anchor Corridor Walkthrough

If you want one concrete slice that explains the repo's design, read this corridor in order:

1. [`PositiveMeasure.lean`](../lean/InfoGeometry/PositiveMeasure.lean)
   Defines bundled strictly positive weights, total mass `Z`, normalization, and generalized KL on the positive cone.
2. [`Projective/Normalize.lean`](../lean/InfoGeometry/Projective/Normalize.lean)
   Shows normalization descends from concrete representatives to projective rays.
3. [`Canonical/PositiveRayCore.lean`](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
   Introduces the canonical projective owner surface: `PositiveRay`, `gaugeSection`, `logDensity`, and `modularPotential`.
4. [`Canonical/RelativePotentialCore.lean`](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
   Separates representative-level and ray-level relative quantities and owns the normalization cocycle `representativeMassShift`.
5. [`Canonical/RelativePotentialCountBridge.lean`](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
   Specializes the representative cocycle to raw positive counts via `countMassShift` and keeps the count presentation explicit.
6. [`Canonical/RelativeSurprisalOperatorLift.lean`](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)
   First-quantizes the scalar story into diagonal operators and shows the same gauge correction survives at the operator level.

This corridor is the repo in miniature:
- start from the lowest natural owner surface
- move upward by adjacent translators
- keep gauge and coherence corrections explicit
- avoid skip-level facade files when an adjacent bridge is the real mathematical object

## Relative Modular Frontier Corridor

This is the current standalone modular frontier. It is intentionally outside the
publication umbrellas and should be read as a mechanical corridor map, not as a
new canopy.

Current direct import chain:

`StandardFormCore -> RelativeModularCore -> RelativeModularProjectiveBridge -> RelativeModularPolarizedBridge -> RelativeModularRecomposition`

Additional side attachment:

- [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean)
  also imports [`PolarizedSector.lean`](../lean/InfoGeometry/Krein/PolarizedSector.lean)
  to realize the plus/minus sector split on the doubled carrier.

| File | Corridor position | File role | Dominant `@[rep_depth ...]` surface | Immediate upstream corridor inputs | Immediate downstream corridor consumers | Umbrella status |
|------|-------------------|-----------|-------------------------------------|------------------------------------|-----------------------------------------|-----------------|
| [`StandardFormCore.lean`](../lean/InfoGeometry/Canonical/StandardFormCore.lean) | root | owner | mixed `krein` / `operator` / `projective` | current modular atom in [`TomitaTakesaki.lean`](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean), projective relative-potential layer | [`RelativeModularCore.lean`](../lean/InfoGeometry/Canonical/RelativeModularCore.lean) | frontier-only |
| [`RelativeModularCore.lean`](../lean/InfoGeometry/Canonical/RelativeModularCore.lean) | root | owner | `projective` | [`StandardFormCore.lean`](../lean/InfoGeometry/Canonical/StandardFormCore.lean) | [`RelativeModularProjectiveBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean), [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean) | frontier-only |
| [`RelativeModularProjectiveBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean) | branch | translator | `projective` | [`RelativeModularCore.lean`](../lean/InfoGeometry/Canonical/RelativeModularCore.lean) | [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean) | frontier-only |
| [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean) | branch | translator | mixed `krein` projector identification plus `projective` sector lift | [`RelativeModularProjectiveBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean), [`PolarizedSector.lean`](../lean/InfoGeometry/Krein/PolarizedSector.lean) | [`RelativeModularRecomposition.lean`](../lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean) | frontier-only |
| [`RelativeModularRecomposition.lean`](../lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean) | leaf | owner | `projective` | [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean) | none in the current corridor | frontier-only |

Mechanical notes:
- `StandardFormCore` is a root owner because it introduces `VectorState`,
  `StandardFormSeed`, `StandardFormCarrier`, and `RelativeModularBridge`.
- `RelativeModularCore` is a root owner because it introduces
  `RelativeStatePair` and `RestrictedRelativeModularData`.
- `RelativeModularProjectiveBridge` is a translator because it adds no new
  modular ontology; it transports restricted data into the
  projective/discrete/count surfaces.
- `RelativeModularPolarizedBridge` is a translator because it identifies the
  seed grading with the spectral grading and realizes restricted data on the
  polarized sheets.
- `RelativeModularRecomposition` is a leaf in the corridor graph, but it is not
  a capstone facade. It is a frontier owner file for recomposition and
  coupling-defect laws.

Current status for capstones / wrappers / public facades on this corridor:
- capstone files: none
- wrapper files: none
- public facade files: none

Umbrella status:
- none of these files are currently imported by
  [`Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean),
  [`All.lean`](../lean/InfoGeometry/All.lean),
  [`InfoGeometry.lean`](../lean/InfoGeometry.lean), or
  [`Library.lean`](../lean/InfoGeometry/Library.lean)
- the whole corridor is therefore frontier-only pending further stabilization

## Generalized Metric Frontier Corridor

This is the doubled/Krein generalized-metric corridor. It stays adjacent to the
existing polarized relative-modular corridor instead of jumping directly to
recomposition or canopy.

Current direct import chain:

`GeneralizedMetricCore -> GeneralizedMetricPolarizedBridge`

Existing owner substrate consumed by this corridor:

- [`TomitaTakesaki.lean`](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean)
  supplies the current doubled-space modular atom `(J, ε, Jε)`.
- [`PolarizedSector.lean`](../lean/InfoGeometry/Krein/PolarizedSector.lean)
  supplies the actual spectral plus/minus split on the doubled carrier.
- [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean)
  supplies the polarized relative-modular carrier package that the translator
  fixes under the canonical generalized-metric projectors.

| File | Corridor position | File role | Dominant `@[rep_depth ...]` surface | Immediate upstream corridor inputs | Immediate downstream corridor consumers | Umbrella status |
|------|-------------------|-----------|-------------------------------------|------------------------------------|-----------------------------------------|-----------------|
| [`GeneralizedMetricCore.lean`](../lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean) | root | owner | `krein` | [`TomitaTakesaki.lean`](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean), [`PolarizedSector.lean`](../lean/InfoGeometry/Krein/PolarizedSector.lean), [`Cartan/Involution.lean`](../lean/InfoGeometry/Cartan/Involution.lean) | [`GeneralizedMetricPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean) | frontier-only |
| [`GeneralizedMetricPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean) | branch | translator | `krein` | [`GeneralizedMetricCore.lean`](../lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean), [`RelativeModularPolarizedBridge.lean`](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean) | none in the current corridor | frontier-only |

Mechanical notes:
- `GeneralizedMetricCore` is a root owner because it introduces the
  generalized-metric seed `(η, S, η ∘ S)`, the induced plus/minus projectors,
  and the canonical specialization to the repo's `(J, ε, Jε)` doubled atom.
- `GeneralizedMetricPolarizedBridge` is a translator because it adds no new
  generalized-metric ontology; it proves that the canonical generalized-metric
  projectors act as exact fixpoint operators on the polarized lifts already
  owned by the relative-modular bridge.

Current status for capstones / wrappers / public facades on this corridor:
- capstone files: none
- wrapper files: none
- public facade files: none

Umbrella status:
- none of these files are currently imported by
  [`Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean),
  [`All.lean`](../lean/InfoGeometry/All.lean),
  [`InfoGeometry.lean`](../lean/InfoGeometry.lean), or
  [`Library.lean`](../lean/InfoGeometry/Library.lean)
- the whole corridor is therefore frontier-only pending further stabilization

## Drazin / EP Frontier Corridor

This is the operator-side generalized-inverse corridor. It is also intentionally
outside the publication umbrellas and should be read as a compact owner map for
partial invertibility, core/nilpotent splitting, descriptor flow, and EP defect
algebra.

Current direct import chain:

`DrazinCoreFlow -> DrazinDescriptorSystems`

Parallel defect branch:

`DrazinCoreFlow -> EPDefectAlgebra`

Existing owner substrate consumed by this corridor:

- [`CertifiedInverseKernel.lean`](../lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean)
  supplies the proof-carrying Drazin and Moore-Penrose witnesses.
- [`InverseKernelAlgebra.lean`](../lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean)
  supplies the spectral/range/domain projector algebra and the dilation-gap
  identities.
- [`EPAndGroupInverse.lean`](../lean/InfoGeometry/Canonical/EPAndGroupInverse.lean)
  supplies the repo-native EP criterion and the group-inverse specialization.

| File | Corridor position | File role | Dominant `@[rep_depth ...]` surface | Immediate upstream corridor inputs | Immediate downstream corridor consumers | Umbrella status |
|------|-------------------|-----------|-------------------------------------|------------------------------------|-----------------------------------------|-----------------|
| [`DrazinCoreFlow.lean`](../lean/InfoGeometry/Canonical/DrazinCoreFlow.lean) | root | owner | `operator` | [`CertifiedInverseKernel.lean`](../lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean), [`InverseKernelAlgebra.lean`](../lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean), [`Drazin.lean`](../lean/InfoGeometry/Canonical/Drazin.lean) | [`DrazinDescriptorSystems.lean`](../lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean), [`EPDefectAlgebra.lean`](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean) | frontier-only |
| [`DrazinDescriptorSystems.lean`](../lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean) | branch | translator | `transport` | [`DrazinCoreFlow.lean`](../lean/InfoGeometry/Canonical/DrazinCoreFlow.lean) | none in the current corridor | frontier-only |
| [`EPDefectAlgebra.lean`](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean) | branch | translator | `operator` | [`DrazinCoreFlow.lean`](../lean/InfoGeometry/Canonical/DrazinCoreFlow.lean), [`EPAndGroupInverse.lean`](../lean/InfoGeometry/Canonical/EPAndGroupInverse.lean) | none in the current corridor | frontier-only |

Mechanical notes:
- `DrazinCoreFlow` is a root owner because it introduces the actual
  `drazinCoreProj` / `nilpotentProj` split, the `corePart` / `nilpotentPart`
  decomposition, and the exact zero-product and nilpotent-power laws.
- `DrazinDescriptorSystems` is a translator because it does not change the
  operator ontology; it transports the core/nilpotent split into exponential
  descriptor-style flow factorization.
- `EPDefectAlgebra` is a translator because it packages existing Moore-Penrose,
  dilation-gap, anomaly, and EP identities into a sharper operator-defect
  surface without introducing a new representation depth.

Current status for capstones / wrappers / public facades on this corridor:
- capstone files: none
- wrapper files: none
- public facade files: none

Umbrella status:
- none of these files are currently imported by
  [`Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean),
  [`All.lean`](../lean/InfoGeometry/All.lean),
  [`InfoGeometry.lean`](../lean/InfoGeometry.lean), or
  [`Library.lean`](../lean/InfoGeometry/Library.lean)
- the whole corridor is therefore frontier-only pending further stabilization

## Read Paths By Task

- Stable publication surface:
  [`InfoGeometry.lean`](../lean/InfoGeometry.lean) ->
  [`Library.lean`](../lean/InfoGeometry/Library.lean) ->
  [`Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean)
- Full project topology:
  [`All.lean`](../lean/InfoGeometry/All.lean) ->
  the relevant subtree `*/All.lean` ->
  the owner files
- Architecture and policy:
  [`Architecture.lean`](../lean/InfoGeometry/Meta/Architecture.lean) ->
  [`Audit.lean`](../lean/InfoGeometry/Audit.lean) ->
  [`lean/DAG/README.md`](../lean/DAG/README.md) ->
  [`tools/infra/README.md`](../tools/infra/README.md)
- First-pass onboarding:
  [`README.md`](../README.md) ->
  [`RepositoryMemoryMap.md`](RepositoryMemoryMap.md) ->
  [`NEWCOMER_PATH.md`](../NEWCOMER_PATH.md) ->
  this page ->
  [`OperationalIntent.md`](OperationalIntent.md)
