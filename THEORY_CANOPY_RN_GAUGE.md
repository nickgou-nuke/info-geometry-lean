# RN / Gauge Canopy

This document is the maintained map for the projective / relative-potential / gauge spine.
These files sit at `@[rep_depth count]` and `@[rep_depth projective]` in the semantic taxonomy
(see `lean/InfoGeometry/Meta/Architecture.lean`).

## Wide substrate (`count` depth)

The wide nonnegative projective layer currently lives in:
- `MeasureProjective`
- `ProjectiveStateCore`
- `RelativeGeneratorCore`

This is the layer where zeros and AE/support-hypothesis semantics are allowed.

## Strict-positive slice (`projective` depth)

The strict-positive pointwise layer currently lives in:
- `PositiveRayCore`
- `RelativePotentialCore`
- `PositiveRayProjectiveBridge`

This is where pointwise `log` and modular-potential formulas are total.

## Representation bridges (`count` → `projective` → `operator`)

Current representation layers include:
- `RelativePotentialDiscreteBridge`
- `RelativePotentialCountBridge`
- `RelativePotentialScalarBridge`
- `KMSSinkhornScalarPotential`
- `CalabiYauRNMongeAmpere`

## Umbrella surface

The maintained public umbrella for this stack is:
- `RedLine`

Other files such as `LogSpineBridge`, `UniversalVolume`, and older multiplicative/additive narratives should be read as presentation layers, not as parallel foundations.
