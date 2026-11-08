import Mathlib.LinearAlgebra.Matrix.Diagonal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Finite Markov mass conservation

This is the finite algebraic conservation law underlying a forward master
equation.  The column-sum hypothesis is explicit; no continuum limit or
probabilistic interpretation is assumed.
-/

namespace InfoGeometry.Probability

open Matrix

variable {n : Type*} [Fintype n]

def forwardMassRate (L : Matrix n n ℝ) (p : n → ℝ) (i : n) : ℝ :=
  ∑ j, L i j * p j

def forwardEulerStep (L : Matrix n n ℝ) (τ : ℝ) (p : n → ℝ) : n → ℝ :=
  fun i => p i + τ * forwardMassRate L p i

def forwardEulerIter (L : Matrix n n ℝ) (τ : ℝ) : ℕ → (n → ℝ) → n → ℝ
  | 0, p => p
  | k + 1, p => forwardEulerStep L τ (forwardEulerIter L τ k p)

theorem sum_forwardMassRate_eq_zero
    (L : Matrix n n ℝ) (p : n → ℝ)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    ∑ i, forwardMassRate L p i = 0 := by
  simp only [forwardMassRate]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp [hcol]

theorem sum_forwardEulerStep_eq_sum
    (L : Matrix n n ℝ) (τ : ℝ) (p : n → ℝ)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    ∑ i, forwardEulerStep L τ p i = ∑ i, p i := by
  simp only [forwardEulerStep, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, sum_forwardMassRate_eq_zero L p hcol]
  simp

theorem sum_forwardEulerIter_eq_sum
    (L : Matrix n n ℝ) (τ : ℝ) (p : n → ℝ)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    ∀ k, ∑ i, forwardEulerIter L τ k p i = ∑ i, p i := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      exact sum_forwardEulerStep_eq_sum L τ (forwardEulerIter L τ k p) hcol |>.trans ih

end InfoGeometry.Probability
