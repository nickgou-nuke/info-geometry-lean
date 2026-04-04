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
