import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The real Apollonius master potential

This file records the algebraic zero-level statement for the real part of
`-log (s / (s - 1))`.  The two foci are excluded explicitly; no distributional
Laplacian or global dynamical claim is made.
-/

namespace InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential

noncomputable section

/-- The squared-distance ratio potential in the `s = sigma + i t` chart. -/
def masterPotential (sigma t : ℝ) : ℝ :=
  (1 / 2) * Real.log (((sigma - 1) ^ 2 + t ^ 2) / (sigma ^ 2 + t ^ 2))

theorem masterPotential_eq_zero_on_criticalLine (t : ℝ) :
    masterPotential (1 / 2) t = 0 := by
  unfold masterPotential
  have hpos : 0 < ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by positivity
  have hratio : (((1 / 2 : ℝ) - 1) ^ 2 + t ^ 2) /
      ((1 / 2 : ℝ) ^ 2 + t ^ 2) = 1 := by
    field_simp
    ring
  rw [hratio, Real.log_one]
  ring

theorem masterPotential_eq_zero_iff_criticalLine
    {sigma t : ℝ}
    (hden : sigma ^ 2 + t ^ 2 ≠ 0)
    (hnum : (sigma - 1) ^ 2 + t ^ 2 ≠ 0) :
    masterPotential sigma t = 0 ↔ sigma = 1 / 2 := by
  unfold masterPotential
  have hdenpos : 0 < sigma ^ 2 + t ^ 2 := by positivity
  have hnumpos : 0 < (sigma - 1) ^ 2 + t ^ 2 := by positivity
  have hratio_pos : 0 < ((sigma - 1) ^ 2 + t ^ 2) / (sigma ^ 2 + t ^ 2) :=
    div_pos hnumpos hdenpos
  constructor
  · intro h
    have hlog : Real.log (((sigma - 1) ^ 2 + t ^ 2) /
        (sigma ^ 2 + t ^ 2)) = 0 := by
      nlinarith
    have hcases := (Real.log_eq_zero).mp hlog
    have hratio : ((sigma - 1) ^ 2 + t ^ 2) /
        (sigma ^ 2 + t ^ 2) = 1 := by
      rcases hcases with hzero | hone | hneg
      · exact False.elim (ne_of_gt hratio_pos hzero)
      · exact hone
      · exact False.elim (by linarith [hratio_pos, hneg])
    field_simp at hratio
    nlinarith
  · intro hs
    rw [hs]
    exact masterPotential_eq_zero_on_criticalLine t

theorem masterPotential_foci_excluded :
    ¬ (0 ^ 2 + 0 ^ 2 = 0 ∧ (0 - 1) ^ 2 + 0 ^ 2 ≠ 0) := by
  norm_num

end

end InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential
