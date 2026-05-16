# Ontology Note

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This file is explicitly non-authoritative.

It records the current conceptual reading that best matches the codebase, but
it does not certify physical, metaphysical, or foundational conclusions.

## Current structural spines

The codebase is now organized most currently (Native Closure Mandated) around these formal spines:

- count / projective / relative-potential language:
  - `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
  - `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
- corrected phase-space / generalized-metric language:
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
  - `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- chirality / polarized / recomposition language:
  - `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`
- KKT / inverse-kernel / conformal / Weyl language:
  - `lean/InfoGeometry/Canonical/KKTCore.lean`
  - `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
  - `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`
- Tomita / Bogoliubov / modular language:
  - `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
  - `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
  - `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

## Current ontological reading

The strongest current (Native Closure Mandated) claim is no longer that the repo is a loose set of
analogies. It is that the repo now contains a real transport architecture with
several exact corridors and a corrected geometric owner lane.

The live ontology is therefore:

- owner packets first;
- adjacent bridges second;
- crown interpretations only where the lower packets already force them.

## What is not yet closed

The codebase does not yet support reading all high-level branches as one fully
closed ontology.

The current remaining gaps are:

- internally deriving the realized-projector to maintained tomita-projector
  identification;
- deriving projector obstruction from trunk-compatible operator data;
- feeding the Weyl branch through that operator theorem; and
- attaching the count/projective trunk to the corrected phase-space trunk at
  the polarized carrier.

Until those are closed, philosophical synthesis should remain secondary.

## Rule for readers

If an ontological claim matters, locate the current owner and bridge files and
inspect the actual Lean declarations. Conceptual prose is not evidence of a
theorem.
