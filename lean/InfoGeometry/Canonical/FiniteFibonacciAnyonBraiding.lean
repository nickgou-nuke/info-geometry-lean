import Mathlib.Data.Nat.Fib.Basic
import InfoGeometry.Canonical.FiniteMajoranaProjectiveBraiding

/-!
# InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding

Finite Fibonacci-anyon braid interfaces.

This file records the finite algebraic core relevant to Fibonacci anyons:

* two topological charges, `𝟙` and `ε`;
* the fusion rule `ε × ε = 𝟙 ⊕ ε`;
* the Fibonacci dimension count for the vacuum channel of `n` Fibonacci anyons;
* the finite/projective braid-word readout inherited from
  `FiniteMajoranaProjectiveBraiding`.

It intentionally does **not** formalize conformal blocks, parafermion CFT,
monodromy matrices, analytic continuation, or physical fault tolerance.  Those
require separate theorem owners.  The result here is the finite algebraic
interface that can safely connect such future data to the existing braid-word
rewrite layer.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding

open FiniteMajoranaBraiding
open FiniteMajoranaProjectiveBraiding

/-- Fibonacci topological charges: vacuum `one` and Fibonacci anyon `eps`. -/
inductive FibonacciCharge where
  /-- Vacuum/trivial charge. -/
  | one
  /-- Fibonacci anyon charge, usually denoted `τ` or `ε`. -/
  | eps
  deriving DecidableEq, Repr

namespace FibonacciCharge

/-- Fusion-output set for Fibonacci charges. -/
def fusion : FibonacciCharge → FibonacciCharge → Finset FibonacciCharge
  | one, a => {a}
  | a, one => {a}
  | eps, eps => {one, eps}

@[simp]
theorem one_fusion (a : FibonacciCharge) :
    fusion one a = {a} := by
  cases a <;> rfl

@[simp]
theorem fusion_one (a : FibonacciCharge) :
    fusion a one = {a} := by
  cases a <;> rfl

/-- The Fibonacci fusion rule: `ε × ε = 𝟙 ⊕ ε`. -/
@[simp]
theorem eps_fusion_eps :
    fusion eps eps = {one, eps} :=
  rfl

/-- Vacuum appears in `ε × ε`. -/
theorem one_mem_eps_fusion_eps :
    one ∈ fusion eps eps := by
  simp

/-- The Fibonacci charge appears in `ε × ε`. -/
theorem eps_mem_eps_fusion_eps :
    eps ∈ fusion eps eps := by
  simp

/-- No third charge appears in `ε × ε`. -/
theorem mem_eps_fusion_eps_iff (a : FibonacciCharge) :
    a ∈ fusion eps eps ↔ a = one ∨ a = eps := by
  cases a <;> simp

end FibonacciCharge

/--
Vacuum-channel dimension for `n` Fibonacci anyons in the standard fusion tree
count.  For `n ≥ 1` this is `fib (n - 1)`; in particular, `2N + 2` anyons have
vacuum-channel dimension `fib (2N + 1)`.
-/
def vacuumFusionDimension (n : ℕ) : ℕ :=
  Nat.fib (n - 1)

/-- The vacuum-channel dimension for `2N + 2` Fibonacci anyons. -/
theorem vacuumFusionDimension_two_mul_add_two (N : ℕ) :
    vacuumFusionDimension (2 * N + 2) = Nat.fib (2 * N + 1) := by
  unfold vacuumFusionDimension
  have h : 2 * N + 2 - 1 = 2 * N + 1 := by omega
  rw [h]

/-- The finite computational space spanned by vacuum fusion channels of `2N + 2` anyons. -/
abbrev FibonacciComputationalSpace (N : ℕ) : Type :=
  Fin (vacuumFusionDimension (2 * N + 2))

/-- The finite computational-space cardinality is the expected Fibonacci number. -/
theorem card_fibonacciComputationalSpace (N : ℕ) :
    Fintype.card (FibonacciComputationalSpace N) = Nat.fib (2 * N + 1) := by
  rw [Fintype.card_fin, vacuumFusionDimension_two_mul_add_two]

/-- Fibonacci braid words use the same finite neighboring-exchange words. -/
abbrev FibonacciBraidWord := List ℕ

/-- A finite projective Fibonacci braid phase assignment. -/
abbrev FibonacciBraidPhase := List ℕ → Units ℂ

/-- Evaluation-factored Fibonacci phases. -/
def fibonacciPhaseOfEval (χ : Equiv.Perm ℕ → Units ℂ) : FibonacciBraidPhase :=
  fun w => χ (FiniteMajoranaBraiding.evalBraidWord w)

/-- Finite projective Fibonacci braid gate readout. -/
def fibonacciProjectiveGate (Gate : Type*) [SMul (Units ℂ) Gate]
    (phase : FibonacciBraidPhase) (readout : Equiv.Perm ℕ → Gate)
    (w : FibonacciBraidWord) : Gate :=
  phase w • readout (FiniteMajoranaBraiding.evalBraidWord w)

/-- Projective Fibonacci gates are invariant under the adjacent braid rewrite. -/
theorem fibonacciProjectiveGate_braid_rewrite_of_phase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (phase : FibonacciBraidPhase) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : FibonacciBraidWord)
    (hphase : phase (left ++ [i, i + 1, i] ++ right) =
      phase (left ++ [i + 1, i, i + 1] ++ right)) :
    fibonacciProjectiveGate Gate phase readout (left ++ [i, i + 1, i] ++ right) =
      fibonacciProjectiveGate Gate phase readout (left ++ [i + 1, i, i + 1] ++ right) := by
  unfold fibonacciProjectiveGate
  rw [hphase, FiniteMajoranaBraiding.evalBraidWord_braid_rewrite]

/-- Projective Fibonacci gates are invariant under separated commutation. -/
theorem fibonacciProjectiveGate_commute_rewrite_of_phase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (phase : FibonacciBraidPhase) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (hsep : i + 1 < j) (left right : FibonacciBraidWord)
    (hphase : phase (left ++ [i, j] ++ right) =
      phase (left ++ [j, i] ++ right)) :
    fibonacciProjectiveGate Gate phase readout (left ++ [i, j] ++ right) =
      fibonacciProjectiveGate Gate phase readout (left ++ [j, i] ++ right) := by
  unfold fibonacciProjectiveGate
  rw [hphase, FiniteMajoranaBraiding.evalBraidWord_commute_rewrite hsep]

/-- Evaluation-factored projective Fibonacci gates are invariant under the braid rewrite. -/
theorem fibonacciProjectiveGate_braid_rewrite_of_evalPhase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : FibonacciBraidWord) :
    fibonacciProjectiveGate Gate (fibonacciPhaseOfEval χ) readout
        (left ++ [i, i + 1, i] ++ right) =
      fibonacciProjectiveGate Gate (fibonacciPhaseOfEval χ) readout
        (left ++ [i + 1, i, i + 1] ++ right) := by
  unfold fibonacciProjectiveGate fibonacciPhaseOfEval
  rw [FiniteMajoranaBraiding.evalBraidWord_braid_rewrite]

/-- Evaluation-factored projective Fibonacci gates are invariant under separated commutation. -/
theorem fibonacciProjectiveGate_commute_rewrite_of_evalPhase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (hsep : i + 1 < j) (left right : FibonacciBraidWord) :
    fibonacciProjectiveGate Gate (fibonacciPhaseOfEval χ) readout (left ++ [i, j] ++ right) =
      fibonacciProjectiveGate Gate (fibonacciPhaseOfEval χ) readout (left ++ [j, i] ++ right) := by
  unfold fibonacciProjectiveGate fibonacciPhaseOfEval
  rw [FiniteMajoranaBraiding.evalBraidWord_commute_rewrite hsep]

end InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
