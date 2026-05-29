import InfoGeometry.Canonical.SuperBracketHestenesKreinClosure
import InfoGeometry.Canonical.FiniteMajoranaBraiding

/-!
# InfoGeometry.Canonical.CayleyMobiusBoundaryBraidClosure

Finite algebraic Cayley--Möbius boundary braid closure.

This file captures the safe theorem-owned core of the intended geometry:
Cayley/Möbius time inversion and compactification are represented as finite
algebraic boundary operations, not as analytic topology.  Boundary states may be
lifted to a double cover, and braid/loop words act by finite permutations while
preserving the boundary sector.

No analytic compactification theorem.
No Poincaré-ball topology.
No loop-group analytic representation.
No physical boundary-state construction.
-/

namespace InfoGeometry.Canonical.CayleyMobiusBoundaryBraidClosure

open InfoGeometry.Canonical.FiniteMajoranaBraiding

/-- Algebraic compactification by adjoining a boundary copy. -/
inductive AlgebraicCompactification (X : Type*) where
  /-- Interior point. -/
  | interior : X → AlgebraicCompactification X
  /-- Boundary point. -/
  | boundary : X → AlgebraicCompactification X
  deriving DecidableEq, Repr

namespace AlgebraicCompactification

variable {X : Type*}

/-- Predicate selecting boundary states. -/
def IsBoundary : AlgebraicCompactification X → Prop
  | interior _ => False
  | boundary _ => True

/-- Predicate selecting interior states. -/
def IsInterior : AlgebraicCompactification X → Prop
  | interior _ => True
  | boundary _ => False

@[simp]
theorem isBoundary_boundary (x : X) :
    IsBoundary (boundary x) :=
  trivial

@[simp]
theorem not_isBoundary_interior (x : X) :
    ¬ IsBoundary (interior x) := by
  simp [IsBoundary]

@[simp]
theorem isInterior_interior (x : X) :
    IsInterior (interior x) :=
  trivial

@[simp]
theorem not_isInterior_boundary (x : X) :
    ¬ IsInterior (boundary x) := by
  simp [IsInterior]

/-- Map both interior and boundary labels by the same finite algebraic map. -/
def map (f : X → X) : AlgebraicCompactification X → AlgebraicCompactification X
  | interior x => interior (f x)
  | boundary x => boundary (f x)

/-- Boundary is preserved by maps induced from the underlying label set. -/
theorem map_preserves_boundary (f : X → X) {p : AlgebraicCompactification X}
    (hp : IsBoundary p) :
    IsBoundary (map f p) := by
  cases p with
  | interior x => cases hp
  | boundary x => simp [map]

/-- Interior is preserved by maps induced from the underlying label set. -/
theorem map_preserves_interior (f : X → X) {p : AlgebraicCompactification X}
    (hp : IsInterior p) :
    IsInterior (map f p) := by
  cases p with
  | interior x => simp [map]
  | boundary x => cases hp

end AlgebraicCompactification

/-- A finite Cayley--Möbius inversion packet: an involution on labels. -/
structure CayleyMobiusInversion (X : Type*) where
  /-- Algebraic time/Möbius inversion map. -/
  inv : X → X
  /-- Involutivity. -/
  inv_inv : ∀ x : X, inv (inv x) = x

namespace CayleyMobiusInversion

variable {X : Type*} (C : CayleyMobiusInversion X)

/-- Inversion induced on the algebraic compactification. -/
def compactifiedInversion :
    AlgebraicCompactification X → AlgebraicCompactification X :=
  AlgebraicCompactification.map C.inv

/-- Compactified inversion is involutive. -/
theorem compactifiedInversion_involutive (p : AlgebraicCompactification X) :
    C.compactifiedInversion (C.compactifiedInversion p) = p := by
  cases p with
  | interior x => simp [compactifiedInversion, AlgebraicCompactification.map, C.inv_inv]
  | boundary x => simp [compactifiedInversion, AlgebraicCompactification.map, C.inv_inv]

/-- Compactified inversion preserves boundary states. -/
theorem compactifiedInversion_preserves_boundary {p : AlgebraicCompactification X}
    (hp : AlgebraicCompactification.IsBoundary p) :
    AlgebraicCompactification.IsBoundary (C.compactifiedInversion p) :=
  AlgebraicCompactification.map_preserves_boundary C.inv hp

end CayleyMobiusInversion

/-- Algebraic double cover of a state space. -/
abbrev DoubleCover (X : Type*) := Bool × X

/-- Deck involution on the algebraic double cover. -/
def deckInvolution {X : Type*} : DoubleCover X → DoubleCover X :=
  fun x => (!x.1, x.2)

/-- The deck involution is involutive. -/
theorem deckInvolution_involutive {X : Type*} (x : DoubleCover X) :
    deckInvolution (deckInvolution x) = x := by
  cases x with
  | mk sheet base => cases sheet <;> rfl

/-- Lift a map to the double cover without changing sheets. -/
def liftToDoubleCover {X : Type*} (f : X → X) : DoubleCover X → DoubleCover X :=
  fun x => (x.1, f x.2)

/-- Sheet-preserving lifts commute with the deck involution. -/
theorem liftToDoubleCover_commutes_deck {X : Type*} (f : X → X) (x : DoubleCover X) :
    liftToDoubleCover f (deckInvolution x) = deckInvolution (liftToDoubleCover f x) := by
  cases x
  rfl

/-- A finite loop/braid action on compactified boundary labels. -/
def braidBoundaryAction (w : BraidWord) :
    AlgebraicCompactification ℕ → AlgebraicCompactification ℕ :=
  AlgebraicCompactification.map (evalBraidWord w)

/-- Braid/loop words preserve the algebraic boundary sector. -/
theorem braidBoundaryAction_preserves_boundary (w : BraidWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsBoundary p) :
    AlgebraicCompactification.IsBoundary (braidBoundaryAction w p) :=
  AlgebraicCompactification.map_preserves_boundary (evalBraidWord w) hp

/-- Braid/loop words preserve the algebraic interior sector. -/
theorem braidBoundaryAction_preserves_interior (w : BraidWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsInterior p) :
    AlgebraicCompactification.IsInterior (braidBoundaryAction w p) :=
  AlgebraicCompactification.map_preserves_interior (evalBraidWord w) hp

/-- Boundary braid action is invariant under adjacent braid rewrites. -/
theorem braidBoundaryAction_braid_rewrite (i : ℕ) (left right : BraidWord) :
    braidBoundaryAction (left ++ [i, i + 1, i] ++ right) =
      braidBoundaryAction (left ++ [i + 1, i, i + 1] ++ right) := by
  funext p
  unfold braidBoundaryAction
  rw [evalBraidWord_braid_rewrite]

/-- Boundary braid action is invariant under separated commutation rewrites. -/
theorem braidBoundaryAction_commute_rewrite {i j : ℕ} (hsep : i + 1 < j)
    (left right : BraidWord) :
    braidBoundaryAction (left ++ [i, j] ++ right) =
      braidBoundaryAction (left ++ [j, i] ++ right) := by
  funext p
  unfold braidBoundaryAction
  rw [evalBraidWord_commute_rewrite hsep]

/-- Lifted boundary braid action on the algebraic double cover. -/
def liftedBraidBoundaryAction (w : BraidWord) :
    DoubleCover (AlgebraicCompactification ℕ) → DoubleCover (AlgebraicCompactification ℕ) :=
  liftToDoubleCover (braidBoundaryAction w)

/-- Lifted boundary braid actions commute with the deck involution. -/
theorem liftedBraidBoundaryAction_commutes_deck (w : BraidWord)
    (x : DoubleCover (AlgebraicCompactification ℕ)) :
    liftedBraidBoundaryAction w (deckInvolution x) =
      deckInvolution (liftedBraidBoundaryAction w x) :=
  liftToDoubleCover_commutes_deck (braidBoundaryAction w) x

end InfoGeometry.Canonical.CayleyMobiusBoundaryBraidClosure
