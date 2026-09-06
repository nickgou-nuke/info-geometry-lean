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
structure AlgebraicStageCompatibility
    (Stage : Nat → Type*) [∀ n, Ring (Stage n)] [∀ n, StarRing (Stage n)]
    (Limit : Type*) [Ring Limit] [StarRing Limit]
    (bond : ∀ n, StarRingHom (Stage n) (Stage (n + 1))) where
  includeStage : ∀ n, StarRingHom (Stage n) Limit
  compatible :
    ∀ n (x : Stage n), includeStage (n + 1) (bond n x) = includeStage n x

namespace AlgebraicStageCompatibility

variable
    {Stage : Nat → Type*} [∀ n, Ring (Stage n)] [∀ n, StarRing (Stage n)]
    {Limit : Type*} [Ring Limit] [StarRing Limit]
    {bond : ∀ n, StarRingHom (Stage n) (Stage (n + 1))}

/--
Readback for one-step compatibility of the explicit stage maps.
-/
theorem include_bond
    (C : AlgebraicStageCompatibility Stage Limit bond)
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
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    SupergradedClosureAt.ImageClosure I (C.includeStage n) :=
  SupergradedClosureAt.map_image_closure I (C.includeStage n)

/-- Square-zero odd lane after inclusion into the target. -/
theorem include_odd_sq_zero
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.Q * C.includeStage n I.Q = 0 :=
  SupergradedClosureAt.map_odd_sq_zero I (C.includeStage n)

/-- Projector/idempotent lane after inclusion into the target. -/
theorem include_parity_idempotent
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.P * C.includeStage n I.P = C.includeStage n I.P :=
  SupergradedClosureAt.map_parity_idempotent I (C.includeStage n)

/-- Odd-odd star closure after inclusion into the target. -/
theorem include_odd_odd_closure
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage n I.Q * star (C.includeStage n I.Q) +
        star (C.includeStage n I.Q) * C.includeStage n I.Q =
      C.includeStage n I.H :=
  SupergradedClosureAt.map_odd_odd_closure I (C.includeStage n)

/-- Parity/odd anticommutation after inclusion into the target. -/
theorem include_parity_odd_anticomm
    (C : AlgebraicStageCompatibility Stage Limit bond)
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
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    SupergradedClosureAt.ImageCentral I (C.includeStage n) :=
  SupergradedClosureAt.map_image_central I (C.includeStage n)

/--
Square-zero closure is unchanged when the next-stage representative is included
through the explicit compatible cone.
-/
theorem include_bond_odd_sq_zero
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage (n + 1) (bond n I.Q) *
        C.includeStage (n + 1) (bond n I.Q) = 0 := by
  rw [C.compatible n I.Q]
  exact include_odd_sq_zero C I

/--
Projector/idempotent closure is unchanged when the next-stage representative is
included through the explicit compatible cone.
-/
theorem include_bond_parity_idempotent
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage (n + 1) (bond n I.P) *
        C.includeStage (n + 1) (bond n I.P) =
      C.includeStage (n + 1) (bond n I.P) := by
  rw [C.compatible n I.P]
  exact include_parity_idempotent C I

/--
Odd-odd star closure is unchanged when the next-stage representative is
included through the explicit compatible cone.
-/
theorem include_bond_odd_odd_closure
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage (n + 1) (bond n I.Q) *
          star (C.includeStage (n + 1) (bond n I.Q)) +
        star (C.includeStage (n + 1) (bond n I.Q)) *
          C.includeStage (n + 1) (bond n I.Q) =
      C.includeStage (n + 1) (bond n I.H) := by
  rw [C.compatible n I.Q, C.compatible n I.H]
  exact include_odd_odd_closure C I

/--
Parity/odd anticommutation is unchanged when the next-stage representative is
included through the explicit compatible cone.
-/
theorem include_bond_parity_odd_anticomm
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage (n + 1) (bond n I.P) *
          C.includeStage (n + 1) (bond n I.Q) +
        C.includeStage (n + 1) (bond n I.Q) *
          C.includeStage (n + 1) (bond n I.P) = 0 := by
  rw [C.compatible n I.P, C.compatible n I.Q]
  exact include_parity_odd_anticomm C I

/--
Image-centrality is unchanged when both representatives are advanced by one
bonding map before inclusion into the explicit target.
-/
theorem include_bond_image_central
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    ∀ X : Stage n,
      C.includeStage (n + 1) (bond n I.C) *
          C.includeStage (n + 1) (bond n X) =
        C.includeStage (n + 1) (bond n X) *
          C.includeStage (n + 1) (bond n I.C) := by
  intro X
  rw [C.compatible n I.C, C.compatible n X]
  exact include_image_central C I X

/--
One-step compatible-cone invariance packet.

This is the algebraic finite-to-target SOP rule: if a finite-stage closure
packet is advanced by one bonding map and then included in the target, the same
image-local closure identities hold there.  No global target centrality,
completion, density, or analytic limit is asserted.
-/
theorem include_bond_image_closure
    (C : AlgebraicStageCompatibility Stage Limit bond)
    {n : Nat}
    (I : SupergradedClosureAt (Stage n)) :
    C.includeStage (n + 1) (bond n I.Q) *
        C.includeStage (n + 1) (bond n I.Q) = 0 ∧
    C.includeStage (n + 1) (bond n I.P) *
        C.includeStage (n + 1) (bond n I.P) =
      C.includeStage (n + 1) (bond n I.P) ∧
    C.includeStage (n + 1) (bond n I.Q) *
          star (C.includeStage (n + 1) (bond n I.Q)) +
        star (C.includeStage (n + 1) (bond n I.Q)) *
          C.includeStage (n + 1) (bond n I.Q) =
      C.includeStage (n + 1) (bond n I.H) ∧
    C.includeStage (n + 1) (bond n I.P) *
          C.includeStage (n + 1) (bond n I.Q) +
        C.includeStage (n + 1) (bond n I.Q) *
          C.includeStage (n + 1) (bond n I.P) = 0 ∧
    (∀ X : Stage n,
      C.includeStage (n + 1) (bond n I.C) *
          C.includeStage (n + 1) (bond n X) =
        C.includeStage (n + 1) (bond n X) *
          C.includeStage (n + 1) (bond n I.C)) := by
  exact
    ⟨include_bond_odd_sq_zero C I,
      include_bond_parity_idempotent C I,
      include_bond_odd_odd_closure C I,
      include_bond_parity_odd_anticomm C I,
      include_bond_image_central C I⟩

end AlgebraicStageCompatibility

end InfoGeometry.Meta.InductiveLimitClosureInterface
