/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinPowerBoundary
import InfoGeometry.Core.NilpotentCartanRegression

/-! A nonzero oblique matrix refutes nilpotence from the two weak inverse laws. -/

namespace InfoGeometry.Core.NilpotentCartanRegression

theorem oblique_not_isNilpotent : ¬ IsNilpotent oblique := by
  have hp : oblique * oblique = oblique := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [oblique, Matrix.mul_apply, Fin.sum_univ_two]
  rintro ⟨n, hn⟩
  have hs : oblique ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [InfoGeometry.Singular.Drazin.pow_succ_eq_of_idempotent hp n] at hs
  have he := congrArg (fun x : RationalMatrix => x 0 1) hs
  norm_num [oblique] at he

theorem oblique_zero_commutes : oblique * (0 : RationalMatrix) = 0 * oblique := by simp

theorem oblique_zero_outer_inverse : (0 : RationalMatrix) * oblique * 0 = 0 := by simp

theorem oblique_zero_residual_not_isNilpotent :
    ¬ IsNilpotent (oblique * (1 - oblique * (0 : RationalMatrix))) := by
  simpa using oblique_not_isNilpotent

end InfoGeometry.Core.NilpotentCartanRegression
