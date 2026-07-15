import InfoGeometry.Canonical.FiniteMajoranaBraiding
import InfoGeometry.Canonical.CayleyMobiusBoundaryBraidClosure

/-!
# InfoGeometry.Canonical.BoundaryLoopSuperClosure

Finite boundary loop closure for the Cayley--Möbius algebraic compactification.

This file extends the finite boundary braid layer with the algebraic closure
properties one expects from loop-word composition and double-cover lifting:

* boundary braid actions compose according to braid-word append;
* boundary preservation is stable under composed loop words;
* lifted boundary braid actions on the double cover also compose;
* Cayley--Möbius inversion commutes with a boundary braid action under an
  explicit finite commutation hypothesis on labels.

No analytic loop group.
No Poincaré-ball topology.
No boundary CFT construction.
-/

namespace BoundaryLoopSuperClosure

open FiniteMajoranaBraiding
open CayleyMobiusBoundaryBraidClosure

/-- A finite loop word is represented by the same finite neighboring-exchange word. -/
abbrev BoundaryLoopWord := List ℕ

/-- Boundary loop action is the finite boundary braid action. -/
def boundaryLoopAction (w : BoundaryLoopWord) :
    AlgebraicCompactification ℕ → AlgebraicCompactification ℕ :=
  AlgebraicCompactification.map (FiniteMajoranaBraiding.evalBraidWord w)

/-- Boundary loop action preserves boundary states. -/
theorem boundaryLoopAction_preserves_boundary (w : BoundaryLoopWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsBoundary p) :
    AlgebraicCompactification.IsBoundary (boundaryLoopAction w p) :=
  AlgebraicCompactification.map_preserves_boundary (FiniteMajoranaBraiding.evalBraidWord w) hp

/-- Boundary loop action preserves interior states. -/
theorem boundaryLoopAction_preserves_interior (w : BoundaryLoopWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsInterior p) :
    AlgebraicCompactification.IsInterior (boundaryLoopAction w p) :=
  AlgebraicCompactification.map_preserves_interior (FiniteMajoranaBraiding.evalBraidWord w) hp

/-- Loop-word append acts by composition of finite boundary actions. -/
theorem boundaryLoopAction_append (u v : BoundaryLoopWord)
    (p : CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ) :
    boundaryLoopAction (u ++ v) p = boundaryLoopAction u (boundaryLoopAction v p) := by
  cases p with
  | interior x =>
      simp [boundaryLoopAction, AlgebraicCompactification.map,
        FiniteMajoranaBraiding.evalBraidWord_append, mul_assoc]
  | boundary x =>
      simp [boundaryLoopAction, AlgebraicCompactification.map,
        FiniteMajoranaBraiding.evalBraidWord_append, mul_assoc]

/-- The empty loop word acts trivially on the algebraic compactification. -/
theorem boundaryLoopAction_nil (p : AlgebraicCompactification ℕ) :
    boundaryLoopAction [] p = p := by
  cases p <;> simp [boundaryLoopAction, AlgebraicCompactification.map]

/-- Adjacent braid rewrites preserve boundary loop actions. -/
theorem boundaryLoopAction_braid_rewrite (i : ℕ) (left right : BoundaryLoopWord) :
    boundaryLoopAction (left ++ [i, i + 1, i] ++ right) =
      boundaryLoopAction (left ++ [i + 1, i, i + 1] ++ right) :=
  by
    funext p
    cases p with
    | interior a =>
        simpa [boundaryLoopAction, AlgebraicCompactification.map] using
          congrArg (fun e => e a)
            (FiniteMajoranaBraiding.evalBraidWord_braid_rewrite i left right)
    | boundary a =>
        simpa [boundaryLoopAction, AlgebraicCompactification.map] using
          congrArg (fun e => e a)
            (FiniteMajoranaBraiding.evalBraidWord_braid_rewrite i left right)

/-- Möbius inversion sees adjacent braid rewrites as the same boundary loop. -/
theorem compactifiedInversion_boundaryLoopAction_braid_rewrite
    (C : CayleyMobiusBoundaryBraidClosure.CayleyMobiusInversion ℕ) (i : ℕ)
    (left right : BoundaryLoopWord)
    (p : CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ) :
    C.compactifiedInversion
        (boundaryLoopAction (left ++ [i, i + 1, i] ++ right) p) =
      C.compactifiedInversion
        (boundaryLoopAction (left ++ [i + 1, i, i + 1] ++ right) p) := by
  simpa using congrArg (fun f => C.compactifiedInversion (f p))
    (boundaryLoopAction_braid_rewrite (i := i) left right)

/-- Separated commutation rewrites preserve boundary loop actions. -/
theorem boundaryLoopAction_commute_rewrite {i j : ℕ} (hsep : i + 1 < j)
    (left right : BoundaryLoopWord) :
    boundaryLoopAction (left ++ [i, j] ++ right) =
      boundaryLoopAction (left ++ [j, i] ++ right) :=
  by
    funext p
    cases p with
    | interior a =>
        simpa [boundaryLoopAction, AlgebraicCompactification.map] using
          congrArg (fun e => e a)
            (FiniteMajoranaBraiding.evalBraidWord_commute_rewrite hsep left right)
    | boundary a =>
        simpa [boundaryLoopAction, AlgebraicCompactification.map] using
          congrArg (fun e => e a)
            (FiniteMajoranaBraiding.evalBraidWord_commute_rewrite hsep left right)

/-- Lift a boundary loop word to the algebraic double cover. -/
def liftedBoundaryLoopAction (w : BoundaryLoopWord) :
    DoubleCover (AlgebraicCompactification ℕ) →
      DoubleCover (AlgebraicCompactification ℕ) :=
  liftToDoubleCover (boundaryLoopAction w)

/-- Lifted loop-word append acts by composition on the double cover. -/
theorem liftedBoundaryLoopAction_append (u v : BoundaryLoopWord)
    (x : CayleyMobiusBoundaryBraidClosure.DoubleCover
      (CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ)) :
    liftedBoundaryLoopAction (u ++ v) x =
      liftedBoundaryLoopAction u (liftedBoundaryLoopAction v x) := by
  cases x with
  | mk sheet p =>
      simp [liftedBoundaryLoopAction, liftToDoubleCover, boundaryLoopAction]
      exact boundaryLoopAction_append u v p

/-- Lifted loop actions commute with the deck involution. -/
theorem liftedBoundaryLoopAction_commutes_deck (w : BoundaryLoopWord)
    (x : CayleyMobiusBoundaryBraidClosure.DoubleCover
      (CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ)) :
    liftedBoundaryLoopAction w (CayleyMobiusBoundaryBraidClosure.deckInvolution x) =
      CayleyMobiusBoundaryBraidClosure.deckInvolution (liftedBoundaryLoopAction w x) :=
  liftToDoubleCover_commutes_deck (boundaryLoopAction w) x

/--
Cayley--Möbius inversion commutes with a boundary loop action when the underlying
finite label maps commute.
-/
theorem compactifiedInversion_commutes_boundaryLoopAction
    (C : CayleyMobiusBoundaryBraidClosure.CayleyMobiusInversion ℕ) (w : BoundaryLoopWord)
    (hcomm : ∀ n : ℕ, C.inv (evalBraidWord w n) = evalBraidWord w (C.inv n))
    (p : CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ) :
    C.compactifiedInversion (boundaryLoopAction w p) =
      boundaryLoopAction w (C.compactifiedInversion p) := by
  cases p with
  | interior x =>
      simp [CayleyMobiusBoundaryBraidClosure.CayleyMobiusInversion.compactifiedInversion,
        boundaryLoopAction, AlgebraicCompactification.map, hcomm]
  | boundary x =>
      simp [CayleyMobiusBoundaryBraidClosure.CayleyMobiusInversion.compactifiedInversion,
        boundaryLoopAction, AlgebraicCompactification.map, hcomm]

/-- A finite packet of boundary loop symmetry data. -/
structure BoundaryLoopClosurePacket where
  /-- Cayley--Möbius inversion. -/
  cayley : CayleyMobiusInversion ℕ
  /-- Loop word acting on boundary labels. -/
  loop : BoundaryLoopWord
  /-- Explicit finite commutation with the Cayley--Möbius inversion. -/
  commutes_with_cayley : ∀ n : ℕ,
    cayley.inv (evalBraidWord loop n) = evalBraidWord loop (cayley.inv n)

namespace BoundaryLoopClosurePacket

/-- The packet loop action preserves boundary states. -/
theorem preserves_boundary (P : BoundaryLoopClosurePacket)
    {p : CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ}
    (hp : CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification.IsBoundary p) :
    CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification.IsBoundary (boundaryLoopAction P.loop p) :=
  boundaryLoopAction_preserves_boundary P.loop hp

/-- The packet Cayley inversion commutes with its loop action. -/
theorem cayley_commutes_loop (P : BoundaryLoopClosurePacket)
    (p : CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ) :
    P.cayley.compactifiedInversion (boundaryLoopAction P.loop p) =
      boundaryLoopAction P.loop (P.cayley.compactifiedInversion p) :=
  compactifiedInversion_commutes_boundaryLoopAction P.cayley P.loop P.commutes_with_cayley p

/-- The packet lifted loop action commutes with the deck involution. -/
theorem lifted_commutes_deck (P : BoundaryLoopClosurePacket)
    (x : CayleyMobiusBoundaryBraidClosure.DoubleCover
      (CayleyMobiusBoundaryBraidClosure.AlgebraicCompactification ℕ)) :
    liftedBoundaryLoopAction P.loop (CayleyMobiusBoundaryBraidClosure.deckInvolution x) =
      CayleyMobiusBoundaryBraidClosure.deckInvolution (liftedBoundaryLoopAction P.loop x) :=
  liftedBoundaryLoopAction_commutes_deck P.loop x

end BoundaryLoopClosurePacket

end BoundaryLoopSuperClosure
