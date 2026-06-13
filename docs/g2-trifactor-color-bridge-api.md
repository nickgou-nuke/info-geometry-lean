# G2 Trifactor Color Bridge API

> Status: finite bridge owner surface
> Owner: `lean/InfoGeometry/Projective/SplitOctonions/G2TrifactorColorBridge.lean`
> Companion witness: `lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsColorStabilizer.lean`

This module packages the finite bridge from the Zorn `OP` projector lane to the
projective quaternion-block color-action lane.

## Proved Statements

- `colorAct_is_stabilizer`
- `colorAct_preserves_splitNorm`
- `colorAct_preserves_splitNorm_null`

## Proof Boundary

- The file proves that the concrete `colorAct` preserves the longitudinal
  block and the split norm of the quaternion-block state.
- It does not identify the stabilizer with `SU(3)`.
- It does not construct `G₂`.
- It does not prove a full `G₂ → SU(3)` theorem.

## Use Case

- Use this module as the canonical finite bridge from the Zorn projector lane
  to the projective split-octonion color-action lane.
- Use [ModuleMap.md](ModuleMap.md) to navigate from the canonical surface to the
  owner file.
