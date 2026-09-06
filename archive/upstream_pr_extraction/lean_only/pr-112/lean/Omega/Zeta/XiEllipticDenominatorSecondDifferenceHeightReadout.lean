import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- The quadratic term in the denominator height expansion has constant discrete second
difference. -/
lemma xi_elliptic_denominator_second_difference_height_readout_quadratic_identity
    (n : ℝ) : (n + 1) ^ 2 + (n - 1) ^ 2 - 2 * n ^ 2 = 2 := by
  ring

/-- Exponentiating the limiting second difference gives the ratio readout. -/
lemma xi_elliptic_denominator_second_difference_height_readout_exp_identity
    (h : ℝ) : Real.exp (2 * h) = Real.exp h * Real.exp h := by
  rw [show (2 : ℝ) * h = h + h by ring, Real.exp_add]

/-- Paper label: `cor:xi-elliptic-denominator-second-difference-height-readout`. -/
theorem paper_xi_elliptic_denominator_second_difference_height_readout :
    (∀ n : ℝ, (n + 1) ^ 2 + (n - 1) ^ 2 - 2 * n ^ 2 = 2) ∧
      (∀ h : ℝ, Real.exp (2 * h) = Real.exp h * Real.exp h) := by
  exact ⟨xi_elliptic_denominator_second_difference_height_readout_quadratic_identity,
    xi_elliptic_denominator_second_difference_height_readout_exp_identity⟩

end Omega.Zeta
