# Cocycle and Detailed-Balance Note

This is a conceptual note, not an authoritative statement of current theorem names.

## Current owner modules

The current cocycle / relative-generator vocabulary is split across:
- `lean/InfoGeometry/Canonical/ProjectiveStateCore.lean`
- `lean/InfoGeometry/Canonical/RelativeGeneratorCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`
- `lean/InfoGeometry/Canonical/RedLine.lean`
- `lean/InfoGeometry/Volume/ConnesCocycle.lean`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/GeneratedFlow.lean`

## Stable structural picture

The repo now distinguishes three layers that older documents often conflated:
- projective nonnegative state language;
- wide relative generator / logarithmic potential language, typically up to AE equivalence or under support hypotheses;
- strict-positive pointwise log-potential language.

At the scalar or strictly positive slice, multiplicative relative density becomes additive log-density, and modular potential is the negative of that log-density. At the wide measure-projective level, the same idea is carried by projective generators rather than naive pointwise formulas.

## Detailed-balance interpretation

Reversible or near-reversible update laws should be read through the current operator and transport owners rather than through older synthesis prose:
- `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`
- `lean/InfoGeometry/Canonical/KMSSinkhornScalarPotential.lean`
- `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`
- `lean/InfoGeometry/Krein/Thermal.lean`

## Verification rule

Use this note only as a map. For current facts, inspect the owner files and the maintained reports.
