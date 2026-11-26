# Doubled-Minkowski BdG/Yang–Mills owner map

This map consolidates the repository-owned formalization of the doubled-Minkowski,
BdG, inductive-colimit, and Yang–Mills lanes. It is an ownership map, not a
new theorem and not a claim that the physical continuum theory has been
constructed.

## Canonical dependency order

```text
DoubledMinkowskiBdGColimitBridge
        │ finite (4,4) metric and BdG square/gap identities
        ▼
DoubledMinkowskiConcreteTowerGap
        │ concrete padding tower and stage gap persistence
        ├──────────────► DoubledMinkowskiBdgDirectLimit
        │                 native DirectLimit carrier and descended Krein form
        │
        └──────────────► BdGColimitGapTransport
                          ring-hom/cone transport of finite BdG squares

DoubledMinkowskiLatticeContinuumLimit
        │ lattice covariant-derivative/Wilson curvature limits
        ▼
DoubledMinkowskiManifoldYangMillsPDE
        │ smooth 4-manifold bundle, Minkowski Hodge operator,
        │ Bianchi identity, self-dual Yang–Mills PDE

TwoSheetedYangMillsInductiveColimit
        │ Peirce/star-ring transport and conditional coercivity/gap bounds
        ▼
OsterwalderSchraderPeirceColimitBridge
        │ OS transfer, Peirce grading, Cl(1,1) tower, Jordan obstruction
```

## Owner assignments

| Mathematical content | Canonical owner | Exact boundary |
|---|---|---|
| Doubled Minkowski `(4,4)` matrices, sheet metrics, Hadamard relation | `lean/InfoGeometry/Canonical/DoubledMinkowskiBdGColimitBridge.lean` | Finite matrix identities |
| Finite BdG particle–hole symmetry and uniform pairing gap | `DoubledMinkowskiBdGColimitBridge.lean` | Finite-dimensional coercive bound; no QFT mass gap |
| Concrete refinement tower and explicit gap-preserving quadratic form | `DoubledMinkowskiConcreteTowerGap.lean` | Padding tower; explicit stage/limit quadratic form |
| Native algebraic direct limit and indefinite descended pairing | `DoubledMinkowskiBdgDirectLimit.lean` | Algebraic `DirectLimit`; no completion or manifold |
| Finite BdG square transport through colimit maps | `lean/InfoGeometry/Physics/BdGColimitGapTransport.lean` | Ring-hom/cone naturality only |
| Lattice-to-continuum covariant derivative and Wilson limits | `lean/InfoGeometry/Lie/DoubledMinkowskiLatticeContinuumLimit.lean` | Analytic small-mesh limits under explicit regularity |
| Smooth manifold gauge bundle, Minkowski Hodge star, Bianchi and YM PDE | `lean/InfoGeometry/Lie/DoubledMinkowskiManifoldYangMillsPDE.lean` | Classical smooth finite-rank manifold carrier |
| Peirce/Yang–Mills star-ring inductive transport | `lean/InfoGeometry/Canonical/TwoSheetedYangMillsInductiveColimit.lean` | Algebraic transport and conditional coercivity |
| OS transfer/Peirce/Cl(1,1) colimit bridge | `lean/InfoGeometry/OperatorAlgebra/OsterwalderSchraderPeirceColimitBridge.lean` | Finite/multi-site OS identities and colimit transport |
| Peirce-to-differential-form carrier issue | `lean/InfoGeometry/Canonical/PeirceToMatrixConnectionCarrierMap.lean` | Proves generic compatibility cannot be inferred |

## Consolidation rule

`DoubledMinkowskiBdgDirectLimit` is the owner of the native algebraic colimit;
`DoubledMinkowskiConcreteTowerGap` is its finite-stage concrete source;
`DoubledMinkowskiBdGColimitBridge` supplies the shared finite metric/BdG
identities and the reusable abstract stability lemma. These are related layers,
not interchangeable replacement APIs.

The repository still lacks a proved carrier map transporting the native BdG
`DirectLimit`—including its connection, Hodge operator, and gap data—into the
smooth Yang–Mills manifold/PDE carrier. Consequently, no continuum Yang–Mills
existence, Wightman/OS reconstruction, or physical mass-gap theorem is claimed.

Spin-instability candidates must reuse the existing
`DoubledMinkowskiSpinFrameInstability` and
`DoubledMinkowskiRotatingSpinInstability` owners rather than introduce another
parallel singlet/triplet API.
