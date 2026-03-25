# RedLine Topic Map

This note tracks the current root language behind the RedLine corridor.

## Current owner modules

The current RedLine stack is:
- `lean/InfoGeometry/Canonical/ProjectiveStateCore.lean`
- `lean/InfoGeometry/Canonical/RelativeGeneratorCore.lean`
- `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialDiscreteBridge.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
- `lean/InfoGeometry/Canonical/RedLine.lean`

Closely related presentation files include:
- `lean/InfoGeometry/Canonical/UniversalVolume.lean`
- `lean/InfoGeometry/Canonical/LogSpineBridge.lean`
- `lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean`

## Current structural reading

The stable spine is now:
- projective positive or nonnegative state below;
- relative generator or relative log-density in the middle;
- scalar, discrete, count, and operator realizations above.

`RedLine.lean` should be read as the umbrella export of that spine, not as a separate ontology.
