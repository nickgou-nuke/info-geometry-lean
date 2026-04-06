# Operational Intent

This repository is one theory with several presentations.
The main burden is not to flatten those presentations into one file-level story,
but to make the morphisms between them explicit, adjacent, and checkable.

## What Is Being Formalized

The stable grammar is the semantic representation ladder defined in
[lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
and enforced by
[lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean).

The active representation depths are:

| `RepDepth` | Meaning |
|---|---|
| `count` | raw counts, positive representatives, mass data |
| `projective` | gauge, positive rays, relative potentials |
| `operator` | diagonal operator lifts, inverse-kernel algebra |
| `krein` | split quadratic, Clifford, doubled and phase-space geometry |
| `transport` | Bogoliubov, Weyl, and related transport layers |
| `thermo` | Gibbs, Sinkhorn, attention, and thermal packaging |

The design rule is:

- owner files define the lowest natural surface
- translator files move one adjacent step
- coherence files prove adjacent composites agree
- capstones summarize lower content without pretending to be roots

## Current Live Trunks

### Count -> projective -> operator

The most stable lower trunk remains:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

This corridor is the clean benchmark for nonvacuous adjacent translation.

### Corrected phase-space generalized-metric trunk

The corrected owner lane is now real and no longer speculative:

- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
- [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)

What is already true on this lane:

- the owner carrier is `E × E*`
- the neutral pairing is explicit
- the generalized-metric owner algebra is closed
- the `B`-twisted realized polarization and realized `±` projectors exist on the doubled carrier

### Polarized and recomposition junction

The corrected owner now reaches the maintained polarized/recomposition lane:

- [PhaseSpacePolarizedBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean)
- [PhaseSpaceRecompositionBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean)

Current status:

- owner-side lifts and transports are real
- realized generalized-metric projector factorization now exists at the junction
- the strongest tomita-facing fixation statements still use explicit identification hypotheses where the final derivation theorem is missing

### KKT, inverse-kernel, and conformal corridor

The corrected owner also now feeds the KKT/conformal side:

- [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
- [EPDefectAlgebra.lean](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean)
- [KKTGeneralizedInverseBridge.lean](../lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean)
- [PhaseSpaceConformalKKTBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean)
- [PhaseSpaceCausalFlowBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean)

This is now a real causal trunk from phase-space owner data to conformal and recomposition leaves.

### Weyl branch

The Weyl branch is partially welded:

- [ConformalAnomalySource.lean](../lean/InfoGeometry/Canonical/ConformalAnomalySource.lean)
- [WeylGaugeField.lean](../lean/InfoGeometry/Canonical/WeylGaugeField.lean)
- [WeylTransport.lean](../lean/InfoGeometry/Canonical/WeylTransport.lean)
- [WeylTransportChiralBridge.lean](../lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean)
- [PhaseSpaceWeylCausalBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean)

The current gap here is not naming. It is a missing operator-level theorem from
trunk data to projector obstruction, then to conformal anomaly source, then to
Weyl holonomy.

## Compatibility Scaffolds

Some important files remain useful but are not the semantic root of the updated theory:

- [ClNN.lean](../lean/InfoGeometry/Clifford/ClNN.lean)
- [ClNNSpecialization.lean](../lean/InfoGeometry/Clifford/ClNNSpecialization.lean)
- [GeneralizedMetricBField.lean](../lean/InfoGeometry/Clifford/GeneralizedMetricBField.lean)
- [GeneralizedMetricPolarizedBridge.lean](../lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean)

These are compatibility or presentation scaffolds, not the corrected owner root.

## What The Tooling Is For

The DAG and infra layers exist to preserve operational memory and expose graph-level pressure:

1. externalize dependency memory from Lean into stable artifacts
2. show owner / translator / coherence / capstone pressure
3. expose vacuity, wrapper growth, and skip-level drift
4. help choose the next file without replacing direct code reading

They do not define truth. Lean source does.

## Immediate Engineering Standard

The next theorem step should always satisfy all of these:

- it materially consumes its hypotheses
- it shortens the distance between a seed owner and a crown leaf
- it removes an explicit identification hypothesis if possible
- it does not introduce a new alias-only surface

## Default Read Order

When context is missing, rebuild it in this order:

1. [README.md](../README.md)
2. [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
3. [docs/Theory.md](Theory.md)
4. [lean/DAG/README.md](../lean/DAG/README.md)
5. [tools/infra/README.md](../tools/infra/README.md)
6. the specific owner and bridge files for the task
