import InfoGeometry.Canonical.BoundaryLoopSuperClosure

/-!
# InfoGeometry.Canonical.FiniteBoundaryLoopAlgebraicClosure

Finite boundary braid closure packaged in the repo-native algebraic language.

This file does not add a new boundary theory.  It simply exposes the already
owned Cayley--Möbius and boundary-loop closure laws under a finite bridge name
that matches the finite boundary braid layer:

* boundary loop words compose by concatenation;
* boundary and interior sectors are preserved;
* the lifted double-cover action commutes with the deck involution;
* Cayley--Möbius inversion commutes with the boundary action when the finite
  label map does.

No analytic loop-group model.
No topological compactification theorem.
No conformal boundary field theory.
-/

namespace FiniteBoundaryLoopAlgebraicClosure

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Canonical.BoundaryLoopSuperClosure
open InfoGeometry.Canonical.CayleyMobiusBoundaryBraidClosure

/-- A finite boundary algebraic-closure packet is just a boundary-loop packet. -/
abbrev FiniteBoundaryAlgebraicClosurePacket := BoundaryLoopClosurePacket

/-- Boundary loop actions are closed under append in the finite algebraic layer. -/
theorem boundaryLoopAction_append_closed (u v : BoundaryLoopWord)
    (p : AlgebraicCompactification ℕ) :
    boundaryLoopAction (u ++ v) p = boundaryLoopAction u (boundaryLoopAction v p) :=
  boundaryLoopAction_append u v p

/-- Boundary loop actions preserve the boundary sector. -/
theorem boundaryLoopAction_preserves_boundary_closed (w : BoundaryLoopWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsBoundary p) :
    AlgebraicCompactification.IsBoundary (boundaryLoopAction w p) :=
  boundaryLoopAction_preserves_boundary w hp

/-- Boundary loop actions preserve the interior sector. -/
theorem boundaryLoopAction_preserves_interior_closed (w : BoundaryLoopWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsInterior p) :
    AlgebraicCompactification.IsInterior (boundaryLoopAction w p) :=
  boundaryLoopAction_preserves_interior w hp

/-- The lifted boundary loop action is closed under composition. -/
theorem liftedBoundaryLoopAction_append_closed (u v : BoundaryLoopWord)
    (x : DoubleCover (AlgebraicCompactification ℕ)) :
    liftedBoundaryLoopAction (u ++ v) x =
      liftedBoundaryLoopAction u (liftedBoundaryLoopAction v x) :=
  liftedBoundaryLoopAction_append u v x

/-- The lifted boundary loop action commutes with the deck involution. -/
theorem liftedBoundaryLoopAction_commutes_deck_closed (w : BoundaryLoopWord)
    (x : DoubleCover (AlgebraicCompactification ℕ)) :
    liftedBoundaryLoopAction w (deckInvolution x) =
      deckInvolution (liftedBoundaryLoopAction w x) :=
  liftedBoundaryLoopAction_commutes_deck w x

/-- Cayley--Möbius inversion commutes with the finite boundary loop action. -/
theorem compactifiedInversion_commutes_boundaryLoopAction_closed
    (C : CayleyMobiusInversion ℕ) (w : BoundaryLoopWord)
    (hcomm : ∀ n : ℕ, C.inv (evalBraidWord w n) = evalBraidWord w (C.inv n))
    (p : AlgebraicCompactification ℕ) :
    C.compactifiedInversion (boundaryLoopAction w p) =
      boundaryLoopAction w (C.compactifiedInversion p) :=
  compactifiedInversion_commutes_boundaryLoopAction C w hcomm p

/-- A finite algebraic closure packet exposes the boundary loop packet readback. -/
structure FiniteBoundaryAlgebraicClosure where
  /-- The underlying boundary-loop packet. -/
  packet : BoundaryLoopClosurePacket

namespace FiniteBoundaryAlgebraicClosure

variable (B : FiniteBoundaryAlgebraicClosure)

/-- Boundary preservation readback for the finite closure packet. -/
theorem preserves_boundary
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsBoundary p) :
    AlgebraicCompactification.IsBoundary (boundaryLoopAction B.packet.loop p) :=
  B.packet.preserves_boundary hp

/-- Cayley--Möbius inversion readback for the finite closure packet. -/
theorem cayley_commutes_loop
    (p : AlgebraicCompactification ℕ) :
    B.packet.cayley.compactifiedInversion (boundaryLoopAction B.packet.loop p) =
      boundaryLoopAction B.packet.loop (B.packet.cayley.compactifiedInversion p) :=
  B.packet.cayley_commutes_loop p

/-- Lifted deck-commutation readback for the finite closure packet. -/
theorem lifted_commutes_deck
    (x : DoubleCover (AlgebraicCompactification ℕ)) :
    liftedBoundaryLoopAction B.packet.loop (deckInvolution x) =
      deckInvolution (liftedBoundaryLoopAction B.packet.loop x) :=
  B.packet.lifted_commutes_deck x

end FiniteBoundaryAlgebraicClosure

end FiniteBoundaryLoopAlgebraicClosure
