import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.ModularLogGenerating
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace InfoGeometry.Canonical

open Real
open scoped BigOperators

/-- The cumulant-generating function C_rho(t) around the physical state rho -/
noncomputable def C_rho {n : ℕ} (ρ : Fin n → ℝ) (t : ℝ) : ℝ :=
  modularLogGenerating ρ (1 - t)

/-- The variance of a function f under a probability distribution p -/
noncomputable def Var_dist {n : ℕ} (p : Fin n → ℝ) (f : Fin n → ℝ) : ℝ :=
  (∑ i, p i * (f i) ^ 2) - (∑ i, p i * f i) ^ 2

/-- Operator surprisal as a function on states -/
noncomputable def K_surprisal_fun {n : ℕ} (ρ : Fin n → ℝ) (i : Fin n) : ℝ :=
  - log (ρ i)

/-- The second derivative of the cumulant-generating function represents the variance of the surprisal.
    We state the variance non-negativity natively here. -/
theorem variance_nonneg {n : ℕ} (p : Fin n → ℝ) (f : Fin n → ℝ) (hp_sum : ∑ i, p i = 1) (hp_nonneg : ∀ i, 0 ≤ p i) :
    0 ≤ Var_dist p f := by
  have H : Var_dist p f = ∑ i, p i * (f i - ∑ j, p j * f j) ^ 2 := by
    dsimp [Var_dist]
    have h_expand : (∑ i, p i * (f i - ∑ j, p j * f j) ^ 2) =
      ∑ i, (p i * (f i) ^ 2 - 2 * (∑ j, p j * f j) * (p i * f i) + (∑ j, p j * f j) ^ 2 * p i) := by
      apply Finset.sum_congr rfl
      intro i _
      have : (f i - ∑ j, p j * f j) ^ 2 = (f i) ^ 2 - 2 * (∑ j, p j * f j) * f i + (∑ j, p j * f j) ^ 2 := by ring
      rw [this]
      ring
    rw [h_expand]
    have h_split : (∑ i, (p i * (f i) ^ 2 - 2 * (∑ j, p j * f j) * (p i * f i) + (∑ j, p j * f j) ^ 2 * p i)) =
      (∑ i, p i * (f i) ^ 2) - (∑ i, 2 * (∑ j, p j * f j) * (p i * f i)) + (∑ i, (∑ j, p j * f j) ^ 2 * p i) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [h_split]
    have h1 : (∑ i, 2 * (∑ j, p j * f j) * (p i * f i)) = 2 * (∑ j, p j * f j) * ∑ i, p i * f i := by
      rw [← Finset.mul_sum]
    have h2 : (∑ i, (∑ j, p j * f j) ^ 2 * p i) = (∑ j, p j * f j) ^ 2 * ∑ i, p i := by
      rw [← Finset.mul_sum]
    rw [h1, h2, hp_sum, mul_one]
    ring
  rw [H]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hp_nonneg i) (sq_nonneg _)

end InfoGeometry.Canonical
