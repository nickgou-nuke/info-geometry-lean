# One Theory, Many Presentations

This repository should be read as one theory with several simultaneous
presentations. The mathematical burden is on the adjacent morphisms:

- define the natural owner at each layer
- move upward by explicit translators
- prove coherence where two adjacent routes meet
- resist facade files that skip the real branch structure

The point is not to make every branch sound the same.
It is to make the branch junctions exact.

## Representation Grammar

The active grammar is the semantic `RepDepth` taxonomy in
[Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean),
checked by [Audit.lean](../lean/InfoGeometry/Audit.lean).

| Depth | Meaning |
|---|---|
| `count` | counts, positive representatives, raw mass data |
| `projective` | positive rays, gauge sections, relative potentials |
| `operator` | operator lifts, projector and inverse-kernel algebra |
| `krein` | split quadratic, doubled, Clifford, phase-space geometry |
| `transport` | Bogoliubov, Weyl, and causal transport |
| `thermo` | Gibbs, Sinkhorn, attention, thermal packaging |

The structural rule is simple:

- non-capstone declarations should move only one depth step at a time
- capstones may span further, but they are consumers, not roots

## Current Semantic Roots

The most important current roots are:

Count/projective roots:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)

Corrected phase-space roots:

- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)

Operator/KKT roots:

- [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
- [EPDefectAlgebra.lean](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean)

Tomita/Bogoliubov roots:

- [TomitaTakesaki.lean](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean)
- [BogoliubovTransport.lean](../lean/InfoGeometry/Canonical/BogoliubovTransport.lean)

## Current Strongest Trunks

### 1. Count -> projective -> operator

This remains the cleanest lower-to-upper corridor:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

This corridor is important because it already has real owner mathematics and a
real cocycle story, not just packaging.

### 2. Corrected phase-space generalized metric

This trunk is now real, not aspirational:

- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
- [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)

What is already closed here:

- the owner carrier `E × E*`
- the neutral pairing
- the generalized-metric involution and projector algebra
- the `B`-twisted realized doubled polarization and realized doubled projectors

This is currently the main geometric trunk of the repo.

### 3. Polarized and recomposition branch

The corrected owner now reaches the existing polarized and recomposition surfaces:

- [PhaseSpacePolarizedBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean)
- [PhaseSpaceRecompositionBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean)

Current state:

- owner-side lifts are real
- owner-side transport is real
- realized generalized-metric projector factorization is now explicit
- the final tomita identification still appears as an explicit hypothesis in the strongest corollaries

So this branch is structurally right, but not fully self-generated yet.

### 4. KKT / inverse-kernel / conformal branch

The corrected owner also reaches:

- [KKTGeneralizedInverseBridge.lean](../lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean)
- [PhaseSpaceConformalKKTBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean)
- [PhaseSpaceCausalFlowBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean)

This gives a genuine causal path from owner-side chirality data to grade-zero
inverse-kernel outputs and conformal packaging.

### 5. Weyl branch

The Weyl branch is now adjacent to the causal trunk:

- [ConformalAnomalySource.lean](../lean/InfoGeometry/Canonical/ConformalAnomalySource.lean)
- [PhaseSpaceWeylCausalBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean)
- [WeylTransport.lean](../lean/InfoGeometry/Canonical/WeylTransport.lean)
- [WeylTransportChiralBridge.lean](../lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean)

The branch now has the operator weld:

trunk data -> projector obstruction operator -> obstruction norm / `chiralScale` -> Weyl holonomy

Right now the remaining work is not branch existence, but tightening hypotheses
inside that source-driven package.

Status update:

- the source-driven operator package is now explicit in
  `PhaseSpaceWeylCausalBridge` (`SourceSpineAndWeylEndpoint`)
- operator-grade block structure and holonomy endpoint are packaged together
- the next burden is reducing explicit commutation/identification hypotheses
  inside that package

## Important Compatibility Scaffolds

The repo still contains valid but non-root presentation scaffolds, especially:

- [ClNN.lean](../lean/InfoGeometry/Clifford/ClNN.lean)
- [ClNNSpecialization.lean](../lean/InfoGeometry/Clifford/ClNNSpecialization.lean)
- [GeneralizedMetricBField.lean](../lean/InfoGeometry/Clifford/GeneralizedMetricBField.lean)
- [GeneralizedMetricPolarizedBridge.lean](../lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean)

These should be kept as compatibility infrastructure until their role is fully
absorbed or strictly reclassified. They are not the semantic root of the
corrected phase-space lane.

## What Is Already Proved

The following structural facts are already real in the codebase:

- the count/projective/operator corridor is a genuine adjacent cocycle corridor
- the corrected phase-space owner exists
- the owner-side generalized-metric algebra is closed
- the corrected owner reaches doubled chirality
- the corrected owner reaches polarized and recomposition transport
- the corrected owner reaches the KKT/conformal branch

This means the repo is already beyond “interesting analogies.”
It now contains real transport architecture.

## What Is Still Missing

The main missing pieces are not more themes. They are closure theorems:

1. derive the realized-projector to tomita-projector identification internally
2. compress the now-explicit source-driven Weyl package by removing avoidable
   commutation/identification hypotheses
3. attach the count/projective seed line to the corrected phase-space line at the polarized junction
4. add one twisted finite-dimensional end-to-end example through the full branch point
5. make the operator anomaly to modular source/sink channel closure explicit as
   a maintained bridge

Until then, the repo has a strong trunk and several genuine leaves, but not a
fully fused forest.

## Near Extensions

The nearest extensions already supported by current code are:

- deeper Tomita / Bogoliubov / modular-flow coherence
- stronger conformal / Weyl obstruction theorems
- finite-dimensional twisted examples

The following are still farther out:

- KK / Atiyah-Singer index anomalies, because the current KK bridge is still thin
- BRST/BV, because the necessary cohomological owner surface is not yet present
- Navier–Stokes style analytic crowns, because the dissipative PDE trunk is not present

So the repo is presently strongest as a geometric-operator transport theory with
phase-space, KKT, conformal, recomposition, and modular branches.
