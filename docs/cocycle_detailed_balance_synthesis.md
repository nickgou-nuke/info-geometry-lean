# Cocycle And Detailed-Balance Note

This is a topic note, not an authoritative statement of current theorem names.

Its job is to point to the current cocycle, relative-potential, and
detailed-balance-adjacent files without pretending that they already form one
closed ontology.

## Current high-confidence files

The current relevant corridor is spread across:

- `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`
- `lean/InfoGeometry/Volume/ConnesCocycle.lean`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
- `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`
- `lean/InfoGeometry/Canonical/KMSSinkhornScalarPotential.lean`
- `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`

## Current reading

The current stable separation is:

- relative-potential and projective owners below;
- cocycle and modular operators in the modular/volume lane;
- detailed-balance-like transport in the Sinkhorn/KMS lane.

These lanes are adjacent, but they should not be collapsed into one theorem
family unless source proves the bridge.

## Current priority

This note is not on the shortest closure path. The main closure work is still on
the corrected phase-space, polarized/recomposition, KKT/conformal, and Weyl
junctions.

## Use rule

Use this note only as a pointer map. For actual statements, read the cited Lean
files.
