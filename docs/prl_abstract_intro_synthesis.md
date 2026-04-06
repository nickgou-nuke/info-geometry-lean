# Publication Note Status

This file is not a live abstract or introduction draft.

It is a reminder that any publication-facing abstract must be regenerated from
the current codebase, not copied from older synthesis prose.

## If you need current source material

Start from the current live trunks:

- count / projective / relative-potential:
  - `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
  - `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
- corrected phase-space / generalized metric:
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
  - `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- polarized / recomposition:
  - `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`
- KKT / conformal / Weyl:
  - `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
  - `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`
- modular / Tomita / Bogoliubov:
  - `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
  - `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
  - `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

Then extract theorem names from source and maintained reports.

## Current rule

No publication-facing prose should describe a closure theorem that the repo does
not yet have.
