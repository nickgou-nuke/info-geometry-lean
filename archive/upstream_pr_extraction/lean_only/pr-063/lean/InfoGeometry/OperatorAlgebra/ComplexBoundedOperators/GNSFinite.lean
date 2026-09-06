import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite-point algebraic GNS model

This is the next step in the Lean reimplementation of the AFP
`Gelfand_Naimark_Segal` construction after the one- and two-point models.
For every finite set `Fin n`, we model the commutative finite C*-algebra
`Fin n → ℂ`.

The file proves the finite algebraic GNS core:

* cyclic vector `Ω = 1`;
* pointwise involution;
* pointwise left action;
* explicit finite inner product `∑ i, star (x i) * y i`;
* cyclicity, representation laws, product/involution law, and the adjoint
  relation for left multiplication.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFinite

open scoped BigOperators

/-- Finite commutative algebra of complex-valued functions on `Fin n`. -/
abbrev FinAlg (n : ℕ) := Fin n → ℂ

/-- Cyclic vector, constantly `1`. -/
def omegaVec (n : ℕ) : FinAlg n := fun _ => 1

/-- Pointwise C*-involution. -/
def involution {n : ℕ} (a : FinAlg n) : FinAlg n := fun i => star (a i)

/-- Pointwise left multiplication. -/
def mulVec {n : ℕ} (a x : FinAlg n) : FinAlg n := fun i => a i * x i

/-- Explicit finite inner product, linear in the second argument. -/
def innerN {n : ℕ} (x y : FinAlg n) : ℂ := ∑ i : Fin n, star (x i) * y i

/-- Vector state induced by `omegaVec`. -/
def omega {n : ℕ} (a : FinAlg n) : ℂ := innerN (omegaVec n) (mulVec a (omegaVec n))

@[simp]
theorem mulVec_apply {n : ℕ} (a x : FinAlg n) (i : Fin n) :
    mulVec a x i = a i * x i := by
  rfl

@[simp]
theorem omegaVec_apply {n : ℕ} (i : Fin n) : omegaVec n i = 1 := by
  rfl

/-- The cyclic vector coefficient recovers the vector state by definition. -/
theorem vector_state_recovers_omega {n : ℕ} (a : FinAlg n) :
    innerN (omegaVec n) (mulVec a (omegaVec n)) = omega a := by
  rfl

/-- Cyclicity: every vector is `a Ω` for `a = x`. -/
theorem cyclic_property {n : ℕ} (x : FinAlg n) :
    ∃ a : FinAlg n, mulVec a (omegaVec n) = x := by
  refine ⟨x, ?_⟩
  funext i
  simp [mulVec, omegaVec]

/-- Left multiplication preserves addition. -/
theorem rep_add {n : ℕ} (a b x : FinAlg n) :
    mulVec (a + b) x = mulVec a x + mulVec b x := by
  funext i
  simp [mulVec]
  ring

/-- Left multiplication sends pointwise multiplication to composition. -/
theorem rep_mul {n : ℕ} (a b x : FinAlg n) :
    mulVec (mulVec a b) x = mulVec a (mulVec b x) := by
  funext i
  simp [mulVec]
  ring

/-- The algebra unit acts as identity. -/
theorem rep_one {n : ℕ} (x : FinAlg n) :
    mulVec 1 x = x := by
  funext i
  simp [mulVec]

/-- The pointwise involution reverses products. -/
theorem involution_mul {n : ℕ} (a b : FinAlg n) :
    involution (mulVec a b) = mulVec (involution b) (involution a) := by
  funext i
  simp [involution, mulVec]
  ring

/-- Algebraic adjoint relation for the finite GNS left action. -/
theorem adjoint_relation {n : ℕ} (a x y : FinAlg n) :
    innerN (mulVec a x) y = innerN x (mulVec (involution a) y) := by
  unfold innerN
  apply Finset.sum_congr rfl
  intro i _
  simp [mulVec, involution]
  ring

/-- The finite vector state is summation over the finite spectrum. -/
theorem omega_eq_sum {n : ℕ} (a : FinAlg n) :
    omega a = ∑ i : Fin n, a i := by
  unfold omega innerN mulVec omegaVec
  apply Finset.sum_congr rfl
  intro i _
  simp

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFinite
