/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.FoldgaugePiEvenzetaFirstDifference

namespace Omega.Conclusion

noncomputable section

/-- The unrestricted remainder term can exactly cancel a nonzero first coefficient
difference at every truncation parameter. -/
theorem foldgauge_first_difference_remainder_can_cancel_everywhere :
    let a : ℕ → ℝ := fun j => if j = 1 then 1 else 0
    let atilde : ℕ → ℝ := fun _ => 0
    let rem : ℕ → ℝ := fun _ => 0
    let remtilde : ℕ → ℝ := fun m =>
      conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale 1 m /
        conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
    let logC : ℕ → ℝ := fun m =>
      Real.log (2 * Real.pi) +
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a 1 m +
          rem m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
    let logCtilde : ℕ → ℝ := fun m =>
      Real.log (2 * Real.pi) +
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde 1 m +
          remtilde m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
    a 1 ≠ atilde 1 ∧ ∀ m, logC m = logCtilde m := by
  dsimp
  let a : ℕ → ℝ := fun j => if j = 1 then 1 else 0
  let atilde : ℕ → ℝ := fun _ => 0
  let rem : ℕ → ℝ := fun _ => 0
  let remtilde : ℕ → ℝ := fun m =>
    conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale 1 m /
      conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
  let logC : ℕ → ℝ := fun m =>
    Real.log (2 * Real.pi) +
      conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a 1 m +
        rem m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
  let logCtilde : ℕ → ℝ := fun m =>
    Real.log (2 * Real.pi) +
      conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde 1 m +
        remtilde m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
  have hq : conclusion_foldgauge_pi_evenzeta_first_difference_q ≠ 0 := by
    dsimp [conclusion_foldgauge_pi_evenzeta_first_difference_q]
    exact ne_of_gt (div_pos Real.goldenRatio_pos (by norm_num))
  constructor
  · simp [a, atilde]
  · intro m
    have hmain :
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a 1 m =
          conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale 1 m := by
      simp [conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum,
        conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale, a]
    have hzero :
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde 1 m = 0 := by
      simp [conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum,
        conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale, atilde]
    have hrem : remtilde m *
        conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m =
          conclusion_foldgauge_pi_evenzeta_first_difference_odd_scale 1 m := by
      dsimp [remtilde]
      exact div_mul_cancel₀ _ (pow_ne_zero _ hq)
    change Real.log (2 * Real.pi) +
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum a 1 m +
          rem m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m =
      Real.log (2 * Real.pi) +
        conclusion_foldgauge_pi_evenzeta_first_difference_partial_sum atilde 1 m +
          remtilde m * conclusion_foldgauge_pi_evenzeta_first_difference_remainder_scale 1 m
    rw [hmain, hzero, hrem]
    simp [rem]

end

end Omega.Conclusion
