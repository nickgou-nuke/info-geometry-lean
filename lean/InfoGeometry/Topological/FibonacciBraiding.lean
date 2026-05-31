import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Categorical.FibonacciBraiding
import InfoGeometry.Canonical.BoundaryLoopSuperClosure

/-!
# InfoGeometry.Topological.FibonacciBraiding

Finite Fibonacci/Cayley boundary braiding.

This module is the safe topological-facing wrapper around the already proved
finite algebraic layers:

* Fibonacci fusion is the finite rule `ε × ε = 𝟙 ⊕ ε`;
* Fibonacci braid words are finite neighboring-exchange words;
* Cayley boundary actions are algebraic maps on the compactified boundary;
* braid rewrites and separated commutations preserve the boundary action;
* lifted boundary actions commute with the algebraic double-cover deck
  involution;
* four-anyon fusion matrices satisfy the finite involutivity/determinant
  readbacks already proved in the canonical layer;
* the matrix packet carrying an explicit Artin witness is imported from the
  categorical layer.

No analytic continuation.
No conformal-block analytic construction.
No universal TQFT theorem.
No fault-tolerance or physical FQH claim.
-/

namespace InfoGeometry.Topological.FibonacciBraiding

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Canonical.CayleyMobiusBoundaryBraidClosure
open InfoGeometry.Canonical.BoundaryLoopSuperClosure

/-! ## Fibonacci fusion readbacks -/

/-- Topological-facing alias for the finite Fibonacci charge type. -/
abbrev BoundaryFibonacciCharge := FibonacciCharge

/-- The finite Fibonacci fusion rule `ε × ε = 𝟙 ⊕ ε`. -/
theorem boundaryFibonacci_fusion_rule :
    FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps =
      {FibonacciCharge.one, FibonacciCharge.eps} :=
  FibonacciCharge.eps_fusion_eps

/-- Vacuum appears in the finite Fibonacci self-fusion rule. -/
theorem boundaryFibonacci_vacuum_mem_self_fusion :
    FibonacciCharge.one ∈ FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps :=
  FibonacciCharge.one_mem_eps_fusion_eps

/-- The Fibonacci charge appears in the finite Fibonacci self-fusion rule. -/
theorem boundaryFibonacci_eps_mem_self_fusion :
    FibonacciCharge.eps ∈ FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps :=
  FibonacciCharge.eps_mem_eps_fusion_eps

/-! ## Jones-style algebraic braid generators -/

/-- A finite Jones/Temperley--Lieb style braid generator `A·1 + A⁻¹e`. -/
def jonesBraidGenerator {R : Type*} [Ring R] (A : Units R) (e : R) : R :=
  (A : R) + ((A⁻¹ : Units R) : R) * e

/-- If the idempotent lane is zero, the Jones-style generator reduces to the unit scalar. -/
@[simp]
theorem jonesBraidGenerator_zero {R : Type*} [Ring R] (A : Units R) :
    jonesBraidGenerator A (0 : R) = A := by
  simp [jonesBraidGenerator]

/-- The Jones-style generator is definitionally the finite algebraic formula. -/
theorem jonesBraidGenerator_def {R : Type*} [Ring R] (A : Units R) (e : R) :
    jonesBraidGenerator A e = (A : R) + ((A⁻¹ : Units R) : R) * e :=
  rfl

/-! ## Cayley boundary braid action for Fibonacci braid words -/

/-- Fibonacci boundary braid words are the finite braid words from the canonical layer. -/
abbrev FibonacciBoundaryWord := FibonacciBraidWord

/-- Finite Fibonacci braid action on the algebraic Cayley boundary. -/
def fibonacciBoundaryAction (w : FibonacciBoundaryWord) :
    AlgebraicCompactification ℕ → AlgebraicCompactification ℕ :=
  boundaryLoopAction w

/-- The empty Fibonacci boundary braid acts trivially. -/
theorem fibonacciBoundaryAction_nil (p : AlgebraicCompactification ℕ) :
    fibonacciBoundaryAction [] p = p :=
  boundaryLoopAction_nil p

/-- Fibonacci boundary braid-word append is finite composition. -/
theorem fibonacciBoundaryAction_append (u v : FibonacciBoundaryWord)
    (p : AlgebraicCompactification ℕ) :
    fibonacciBoundaryAction (u ++ v) p =
      fibonacciBoundaryAction u (fibonacciBoundaryAction v p) :=
  boundaryLoopAction_append u v p

/-- Fibonacci boundary braids preserve boundary labels. -/
theorem fibonacciBoundaryAction_preserves_boundary (w : FibonacciBoundaryWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsBoundary p) :
    AlgebraicCompactification.IsBoundary (fibonacciBoundaryAction w p) :=
  boundaryLoopAction_preserves_boundary w hp

/-- Fibonacci boundary braids preserve interior labels. -/
theorem fibonacciBoundaryAction_preserves_interior (w : FibonacciBoundaryWord)
    {p : AlgebraicCompactification ℕ}
    (hp : AlgebraicCompactification.IsInterior p) :
    AlgebraicCompactification.IsInterior (fibonacciBoundaryAction w p) :=
  boundaryLoopAction_preserves_interior w hp

/-- Adjacent Artin braid rewrites preserve the finite Fibonacci boundary action. -/
theorem fibonacciBoundaryAction_braid_rewrite (i : ℕ) (left right : FibonacciBoundaryWord) :
    fibonacciBoundaryAction (left ++ [i, i + 1, i] ++ right) =
      fibonacciBoundaryAction (left ++ [i + 1, i, i + 1] ++ right) :=
  boundaryLoopAction_braid_rewrite i left right

/-- Separated Artin commutation rewrites preserve the finite Fibonacci boundary action. -/
theorem fibonacciBoundaryAction_commute_rewrite {i j : ℕ} (hsep : i + 1 < j)
    (left right : FibonacciBoundaryWord) :
    fibonacciBoundaryAction (left ++ [i, j] ++ right) =
      fibonacciBoundaryAction (left ++ [j, i] ++ right) :=
  boundaryLoopAction_commute_rewrite hsep left right

/-- Lifted Fibonacci boundary action on the algebraic double cover. -/
def liftedFibonacciBoundaryAction (w : FibonacciBoundaryWord) :
    DoubleCover (AlgebraicCompactification ℕ) → DoubleCover (AlgebraicCompactification ℕ) :=
  liftedBoundaryLoopAction w

/-- Lifted Fibonacci boundary actions commute with the deck involution. -/
theorem liftedFibonacciBoundaryAction_commutes_deck (w : FibonacciBoundaryWord)
    (x : DoubleCover (AlgebraicCompactification ℕ)) :
    liftedFibonacciBoundaryAction w (deckInvolution x) =
      deckInvolution (liftedFibonacciBoundaryAction w x) :=
  liftedBoundaryLoopAction_commutes_deck w x

/-! ## Four-anyon finite matrix readbacks -/

/-- Topological-facing alias for a finite four-Fibonacci-anyon fusion packet. -/
abbrev FourFibonacciAnyonPacket := FourAnyonFusionPacket

/-- The finite four-anyon fusion matrix is involutive. -/
theorem fourFibonacciAnyon_F_sq (P : FourFibonacciAnyonPacket) :
    P.F * P.F = 1 :=
  FourAnyonFusionPacket.F_sq P

/-- The finite four-anyon fusion matrix has determinant `-1`. -/
theorem fourFibonacciAnyon_det_F (P : FourFibonacciAnyonPacket) :
    P.F.det = -1 :=
  FourAnyonFusionPacket.det_F P

/-- The finite middle braid generator is the algebraic conjugate `F R F`. -/
theorem fourFibonacciAnyon_B_eq_FRF (P : FourFibonacciAnyonPacket) :
    P.B = P.F * P.R * P.F :=
  FourAnyonFusionPacket.B_eq_FRF P

end InfoGeometry.Topological.FibonacciBraiding
