import InfoGeometry.Meta.InductiveInvariantPacket

/-!
# InfoGeometry.Meta.InductiveLimitClosureInterface

Algebraic interface for sending finite supergraded closure packets into a
candidate limit carrier.

This file deliberately does not construct a topological or analytic completion.
It records only explicit star-preserving stage maps into a target algebra and
proves the image-local closure facts that follow from those maps.

No density result.
No continuity result.
No completion result.
No global centrality result for arbitrary target elements.
-/

namespace InfoGeometry.Meta.InductiveLimitClosureInterface

open InfoGeometry.Meta.InductiveInvariantPacket

/--
Explicit algebraic cone from a staged star-ring system into a target star-ring.

The field `compatible` says the chosen target inclusion agrees with each
one-step bonding map.  No topology or completion is included here.
-/
structure AlgebraicLimitCone
    (Stage : Nat → Type*) [∀ n, Ring (Stage n)] [∀ n, StarRing (Stage n)]
    (Limit : Type*) [Ring Limit] [StarRing Limit]
    (bond : ∀ n, StarRingHom (Stage n) (Stage (n + 1))) where
  includeStage : ∀ n, StarRingHom (Stage n) Limit
  compatible :
    ∀ n (x : Stage n), includeStage (n + 1) (bond n x) = includeStage n x

namespace AlgebraicLimitCone

variable
    {Stage : Nat → Type*} [∀ n, Ring (Stage n)] [∀ n, StarRing (Stage n)]
    {Limit : Type*} [Ring Limit] [StarRing Limit]
    {bond : ∀ n, StarRingHom (Stage n) (Stage (n + 1))}

/--
Readback for one-step compatibility of the explicit stage maps.
-/
theorem include_bond
    (C : AlgebraicLimitCone Stage Limit bond)
    (n : Nat) (x : Stage n) :
    C.includeStage (n + 1) (bond n x) = C.includeStage n x :=
  C.compatible n x

/--
Any finite-stage closure packet has its closure relations preserved on its
image in the target algebra.

This is image-local.  It does not say that the central lane commutes with every
element of the target.
-/
theorem stage_image_closure
    (C : AlgebraicLimitCone Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    SupergradedClosureAt.ImageClosure I (C.includeStage n) :=
  SupergradedClosureAt.map_image_closure I (C.includeStage n)

/-- Square-zero odd lane after inclusion into the target. -/
theorem include_odd_sq_zero
    (C : AlgebraicLimitCone Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.Q * C.includeStage n I.Q = 0 :=
  SupergradedClosureAt.map_odd_sq_zero I (C.includeStage n)

/-- Projector/idempotent lane after inclusion into the target. -/
theorem include_parity_idempotent
    (C : AlgebraicLimitCone Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.P * C.includeStage n I.P = C.includeStage n I.P :=
  SupergradedClosureAt.map_parity_idempotent I (C.includeStage n)

/-- Odd-odd star closure after inclusion into the target. -/
theorem include_odd_odd_closure
    (C : AlgebraicLimitCone Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.Q * star (C.includeStage n I.Q) +
        star (C.includeStage n I.Q) * C.includeStage n I.Q =
      C.includeStage n I.H :=
  SupergradedClosureAt.map_odd_odd_closure I (C.includeStage n)

/-- Parity/odd anticommutation after inclusion into the target. -/
theorem include_parity_odd_anticomm
    (C : AlgebraicLimitCone Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.P * C.includeStage n I.Q +
        C.includeStage n I.Q * C.includeStage n I.P = 0 :=
  SupergradedClosureAt.map_parity_odd_anticomm I (C.includeStage n)

/--
Centrality on the image of the finite stage after inclusion into the target.

This is the correct unconditional limit-interface statement:
`includeStage n I.C` commutes with elements also coming from `Stage n`.
-/
theorem include_image_central
    (C : AlgebraicLimitCone Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    SupergradedClosureAt.ImageCentral I (C.includeStage n) :=
  SupergradedClosureAt.map_image_central I (C.includeStage n)

end AlgebraicLimitCone

end InfoGeometry.Meta.InductiveLimitClosureInterface
