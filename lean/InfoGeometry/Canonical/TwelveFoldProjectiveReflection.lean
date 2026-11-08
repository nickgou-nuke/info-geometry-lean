import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinSixStateBundle
import InfoGeometry.Canonical.TwelveFoldExplicitOperators

open scoped Matrix

namespace InfoGeometry.Canonical.TwelveFoldProjectiveReflection

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.KleinSixStateBundle
open InfoGeometry.Canonical.TwelveFoldExplicitOperators

noncomputable section

private theorem sheet_conjugate_omegaChi_cube :
    sheetExchange * (omegaChi ^ 3) * sheetExchange =
      (-Complex.I) • omegaChi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omegaChi, uPlus, uMinus, sheetExchange, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I, pow_succ]

private theorem color_conjugate_shift_sq :
    colorReflection * (colorShift ^ 2) * colorReflection = colorShift := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorReflection, colorShift, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two]

private theorem masterTwelve_pow_eleven :
    masterTwelve ^ 11 = Matrix.kronecker omegaChi colorShift := by
  have hpow (A : Matrix (Fin 2) (Fin 2) ℂ)
      (B : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ) :
      (Matrix.kronecker A B) ^ n =
        Matrix.kronecker (A ^ n) (B ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, pow_succ, kronecker_mul, pow_succ]
  rw [masterTwelve_eq_kronecker, hpow]
  have hω : (omegaChi ^ 3) ^ 11 = omegaChi := by
    rw [← pow_mul]
    calc
      omegaChi ^ (3 * 11) = omegaChi ^ (4 * 8 + 1) := by norm_num
      _ = omegaChi ^ (4 * 8) * omegaChi := by
        rw [pow_add]
        simp
      _ = omegaChi := by
        rw [show omegaChi ^ (4 * 8) = (omegaChi ^ 4) ^ 8 by rw [pow_mul],
          omegaChi_four]
        simp
  have hX : (colorShift ^ 2) ^ 11 = colorShift := by
    rw [← pow_mul]
    calc
      colorShift ^ (2 * 11) = colorShift ^ (3 * 7 + 1) := by norm_num
      _ = colorShift ^ (3 * 7) * colorShift := by
        rw [pow_add]
        simp
      _ = colorShift := by
        rw [show colorShift ^ (3 * 7) = (colorShift ^ 3) ^ 7 by rw [pow_mul],
          colorShift_cubed]
        simp
  rw [hω, hX]

theorem masterTwelve_pow_eleven_mul_masterTwelve :
    masterTwelve ^ 11 * masterTwelve =
      (1 : TwelveFoldExplicitOperators.Mat23C) := by
  rw [← pow_succ]
  exact masterTwelve_twelve

theorem masterTwelve_mul_pow_eleven :
    masterTwelve * masterTwelve ^ 11 =
      (1 : TwelveFoldExplicitOperators.Mat23C) := by
  rw [← pow_succ']
  exact masterTwelve_twelve

theorem theta_masterTwelve_theta :
    theta * masterTwelve * theta =
      (-Complex.I) • masterTwelve ^ 11 := by
  calc
    theta * masterTwelve * theta =
        Matrix.kronecker (sheetExchange * omegaChi ^ 3 * sheetExchange)
          (colorReflection * colorShift ^ 2 * colorReflection) := by
      rw [theta, masterTwelve_eq_kronecker, kronecker_mul, kronecker_mul]
    _ = Matrix.kronecker ((-Complex.I) • omegaChi) colorShift := by
      rw [sheet_conjugate_omegaChi_cube, color_conjugate_shift_sq]
    _ = (-Complex.I) • Matrix.kronecker omegaChi colorShift := by
      simpa using Matrix.smul_kronecker (-Complex.I) omegaChi colorShift
    _ = (-Complex.I) • masterTwelve ^ 11 := by rw [masterTwelve_pow_eleven]

theorem theta_masterTwelve_sq_theta :
    theta * masterTwelve ^ 2 * theta = -(masterTwelve ^ 2) ^ 5 := by
  calc
    theta * masterTwelve ^ 2 * theta = theta * triality * theta := by
      rw [masterTwelve_sq]
      rfl
    _ = -triality ^ 5 := theta_triality_theta
    _ = -(masterTwelve ^ 2) ^ 5 := by
      rw [masterTwelve_sq]
      rfl

end
end InfoGeometry.Canonical.TwelveFoldProjectiveReflection
