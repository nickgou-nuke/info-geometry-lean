# Theory Audit Report

Generated: 2026-03-09 08:53:34Z

## Build toolchain status
- lake: available (/usr/bin/lake)
```bash
Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)
```
Generated: 2026-03-09 06:23:13Z

## Build toolchain status
- lake: unavailable on PATH
- lake fallback: not found at ~/.elan/bin/lake

## Placeholder proof debt (sorry/admit)

```text
lean/InfoGeometry/Krein/Metric.lean:41:  sorry
lean/InfoGeometry/Canonical/IBCore.lean:114:      sorry
lean/InfoGeometry/Canonical/IBCore.lean:133:  sorry
lean/InfoGeometry/Canonical/IBCore.lean:158:  sorry
```

- Total placeholder occurrences in canonical tree: 4

## Axiom declarations

```text
```
- Total explicit axiom declarations: 0

## Namespace audit

```text
[audit] Project namespace: InfoGeometry
[audit] Scanning root:       ./lean/InfoGeometry

[audit] Files with namespace InfoGeometry*: 239
[audit] Files missing namespace InfoGeometry*: 53

=== Missing namespace InfoGeometry ===
./lean/InfoGeometry/All.lean
./lean/InfoGeometry/Canonical/Algebra.lean
./lean/InfoGeometry/Canonical/All.lean
./lean/InfoGeometry/Canonical/Clifford.lean
./lean/InfoGeometry/Canonical/DrazinAdjoint.lean
./lean/InfoGeometry/Canonical/Foundations.lean
./lean/InfoGeometry/Canonical/GeneralizedKL.lean
./lean/InfoGeometry/Canonical/Geometry.lean
./lean/InfoGeometry/Canonical/GrandCanonicalCore.lean
./lean/InfoGeometry/Canonical/KK.lean
./lean/InfoGeometry/Canonical/KKFoundation.lean
./lean/InfoGeometry/Canonical/Krein.lean
./lean/InfoGeometry/Canonical/KreinNaturalFlow.lean
./lean/InfoGeometry/Canonical/MoorePenroseAdjoint.lean
./lean/InfoGeometry/Canonical/Prequantum.lean
./lean/InfoGeometry/Canonical/Projective.lean
./lean/InfoGeometry/Canonical/Quantum.lean
./lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean
./lean/InfoGeometry/Canonical/Statistics.lean
./lean/InfoGeometry/Canonical/Thermo.lean
./lean/InfoGeometry/Canonical/Twistor.lean
./lean/InfoGeometry/Cartan.lean
./lean/InfoGeometry/Clifford/Cl11.lean
./lean/InfoGeometry/Clifford/Grading.lean
./lean/InfoGeometry/Clifford/Lift.lean
./lean/InfoGeometry/Clifford/Relations.lean
./lean/InfoGeometry/Clifford/Supercharge.lean
./lean/InfoGeometry/Convex.lean
./lean/InfoGeometry/Core.lean
./lean/InfoGeometry/Core/Derivatives.lean
./lean/InfoGeometry/Cramer.lean
./lean/InfoGeometry/ExponentialFamily.lean
./lean/InfoGeometry/Generated.lean
./lean/InfoGeometry/Krein/All.lean
./lean/InfoGeometry/Krein/Category.lean
./lean/InfoGeometry/Krein/KreinSpace.lean
./lean/InfoGeometry/Krein/Prelude.lean
./lean/InfoGeometry/Krein/State.lean
./lean/InfoGeometry/Krein/Superalgebra.lean
./lean/InfoGeometry/Krein/TestTimeout.lean
./lean/InfoGeometry/Krein/Thermal.lean
./lean/InfoGeometry/LLM.lean
./lean/InfoGeometry/Library.lean
./lean/InfoGeometry/MaxEnt.lean
./lean/InfoGeometry/MaxEnt/JaynesInfoStatMechTest.lean
./lean/InfoGeometry/OptimalTransport.lean
./lean/InfoGeometry/Potential.lean
./lean/InfoGeometry/Projective/Null.lean
./lean/InfoGeometry/Projective/ProjectiveMap.lean
./lean/InfoGeometry/Projective/Rays.lean
./lean/InfoGeometry/Singular.lean
./lean/InfoGeometry/SuperUnified.lean
./lean/InfoGeometry/generalizedKL.lean

=== Files declaring a non-InfoGeometry namespace (heuristic) ===
./lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean :: 26:namespace FUSION
./lean/InfoGeometry/Krein/Category.lean :: 25:namespace Krein
./lean/InfoGeometry/Krein/KreinSpace.lean :: 54:namespace KreinSpace
./lean/InfoGeometry/Krein/State.lean :: 26:namespace KreinStateSpace
./lean/InfoGeometry/Krein/Superalgebra.lean :: 7:namespace KreinGradedModule

=== Namespace prefix histogram (first namespace line per file) ===
    243 InfoGeometry
      5 SymmetricLieAlgebra
      5 PositiveMeasure
      3 ProjectivePrequantumBundle
      2 YangMillsMassGapBridge
      2 TransformerBlock
      2 MaskedTransformerBlock
      2 LogPotential
      2 KreinSpace
      2 KreinGradedModule
      1 alphaConnection
      1 TwistedGaussianFamily
      1 ThermalModel
      1 ThermalDiagonal
      1 SymmetricCliffordModule
      1 SuperTraceLike
      1 StrongRicciFromHessian
      1 StrictProbabilityDist
      1 StatisticalMechanics
      1 SpectralTriple
      1 SUNGaugeInstantiation
      1 RegularizedSpectralTriple
      1 QFTAxiomsLayer
      1 Projector
      1 ProjectiveDynamics
      1 ProjectiveBridge
      1 ProbDist
      1 PrequantumData
      1 PositionalEncoding
      1 OneD

[audit] Done.
```

## Orphaned Lean file audit

```text
[orphaned-check] OK
```

## Notes
- This report is static when lake is unavailable; full proof checking requires successful lake build.
