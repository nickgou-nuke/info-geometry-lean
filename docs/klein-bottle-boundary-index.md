# Klein Bottle Boundary Index

> Status: finite and conditional topology packet
> Audited: 2026-06-11
> Scope: `Z2` glide-reflection boundary action, Klein gluing trace closure, and
> orientifold hypothesis bridge
> Boundary: this document does not claim a constructed analytic Klein bottle,
> a global prime-gas quotient, or a derived orientifold model.

This index records the current theorem-owned Klein-bottle boundary lane.

## Active Owner Files

- [lean/InfoGeometry/Canonical/KleinBottleTopology.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinBottleTopology.lean)
- [lean/InfoGeometry/Canonical/KleinBottleOrientifold.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinBottleOrientifold.lean)
- [lean/InfoGeometry/Canonical/KleinBottleBoundaryAction.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinBottleBoundaryAction.lean)

## Proof Strength

| Surface | Closed content | Conditional content | Not proved |
|---|---|---|---|
| `KleinBottleTopology.lean` | Defines `klein_gluing M P = P * M * Pᵀ`; proves trace closure from `Pᵀ * P = 1` and `trace M = 0`. | Orthogonality and trace balance are hypotheses. | Global quotient topology, analytic boundary construction. |
| `KleinBottleOrientifold.lean` | Records orientifold hypothesis names in a kernel-safe packet. | All orientifold effects remain proposition fields to be supplied by a concrete model. | Derivation of Möbius parity, square-free support, anomaly cancellation from geometry. |
| `KleinBottleBoundaryAction.lean` | Proves finite `Z2` sheet reflection, deck translation, commuting generators, and glide-reflection involution on a two-bit boundary cell. | Connects `klein_gluing` to the orientifold packet only when `orientationReversingProjection` and `kleinBottleQuotient` are explicitly supplied. | Analytic prime-gas realization, actual topological quotient space, global Klein-bottle Fock model. |

## Readout

The theorem-owned finite story is:

1. `sheetReflection` and `deckTranslation` are involutive `Z2` actions.
2. Their composite `glideReflection` is also involutive in the finite boundary
   cell model.
3. The existing `klein_gluing` boundary operator preserves zero trace under an
   orthogonal parity twist.
4. The orientifold bridge packages this trace closure together with explicit
   orientifold hypotheses, without deriving those hypotheses.

## Inactive Generated Surfaces

The workspace currently also contains generated files such as
`KleinBottleBoundaryActionPacket.lean` and
`KleinBottleOrientifoldBoundaryBridge.lean`. They are not imported in
`Canonical/All.lean` at the time of this audit. The active owner for this pass
is `KleinBottleBoundaryAction.lean`, which compiles and is imported.

## Verification

```bash
lake env lean lean/InfoGeometry/Canonical/KleinBottleBoundaryAction.lean
lake build InfoGeometry.Canonical.KleinBottleBoundaryAction
lake env lean lean/InfoGeometry/Canonical/All.lean
lake env lean lean/InfoGeometry/All.lean
```
