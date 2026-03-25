# RN / Gauge Canopy

This document is the maintained map for the projective / relative-potential / gauge spine.

## Wide substrate

The wide nonnegative projective layer currently lives in:
- `MeasureProjective`
- `ProjectiveStateCore`
- `RelativeGeneratorCore`

This is the layer where zeros and AE/support-hypothesis semantics are allowed.

## Strict-positive slice

The strict-positive pointwise layer currently lives in:
- `PositiveRayCore`
- `RelativePotentialCore`
- `PositiveRayProjectiveBridge`

This is where pointwise `log` and modular-potential formulas are total.

## Representation bridges

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
