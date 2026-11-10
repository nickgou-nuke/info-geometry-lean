/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinPowerBoundary
import InfoGeometry.Core.NilpotentCartanRegression

/-! A nonzero oblique matrix refutes nilpotence from the two weak inverse laws. -/

namespace InfoGeometry.Core.NilpotentCartanRegression

/-- The oblique idempotent is not nilpotent. -/
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

/--
The zero operator is an outer inverse of the nonzero oblique idempotent and
commutes with it, but these two weak laws do not force a Drazin index: the
resulting residual is the original non-nilpotent operator.
-/
theorem zero_outer_inverse_does_not_force_drazin_index :
    oblique * (0 : RationalMatrix) = 0 * oblique ∧
    (0 : RationalMatrix) * oblique * 0 = 0 ∧
    oblique ≠ 0 ∧
    ¬ IsNilpotent (oblique * (1 - oblique * (0 : RationalMatrix))) ∧
    ¬ ∃ k, InfoGeometry.Canonical.Drazin.IsDrazinInverse oblique 0 k := by
  have hcomm : oblique * (0 : RationalMatrix) = 0 * oblique := by simp
  have houter : (0 : RationalMatrix) * oblique * 0 = 0 := by simp
  have hres : oblique * (1 - oblique * (0 : RationalMatrix)) = oblique := by simp
  have hnot : ¬ IsNilpotent (oblique * (1 - oblique * (0 : RationalMatrix))) := by
    rw [hres]
    exact oblique_not_isNilpotent
  refine ⟨hcomm, houter, ?_, hnot, ?_⟩
  · intro hzero
    have hentry := congrArg (fun A : RationalMatrix => A 0 1) hzero
    norm_num [oblique] at hentry
  · intro hdrazin
    have hresNilpotent : IsNilpotent (oblique * (1 - oblique * (0 : RationalMatrix))) := by
      exact (InfoGeometry.Canonical.Drazin.residual_isNilpotent_iff_exists_drazinIndex
        hcomm houter).2 hdrazin
    exact hnot hresNilpotent

end InfoGeometry.Core.NilpotentCartanRegression
