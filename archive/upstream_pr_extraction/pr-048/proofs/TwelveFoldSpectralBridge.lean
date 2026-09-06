import proofs.TwelveFoldSheetColorOmega
import proofs.SixStateCharacteristicPolynomial
import Mathlib.GroupTheory.OrderOfElement

/-!
# Spectral bridge for the twelvefold master operator

The carrier remains six-dimensional.  The master operator has six labelled
eigenvectors, while its order combines a cubic colour character with a
quartic sheet character.
-/

noncomputable section
namespace TwelveFoldSpectralBridge

open TwoSheetThreeColorWeyl TwelveFoldSheetColorOmega
open HexagonalSixRootTiling SixStateSpectralBridge

def masterEigenvalue (ω : ℂ) (n : HexIndex) : ℂ :=
  match sheetOf n with
  | .positive => colorEigenvalue ω (colorOf n) ^ 2
  | .negative => -Complex.I * colorEigenvalue ω (colorOf n) ^ 2

theorem omegaSheet_cube_eigen_positive :
    (omegaSheet ^ 3).mulVec (sheetVector .positive) =
      sheetVector .positive := by
  funext i
  fin_cases i <;>
    simp [omegaSheet, sheetPlus, sheetMinus, sheetVector, pow_succ,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

theorem omegaSheet_cube_eigen_negative :
    (omegaSheet ^ 3).mulVec (sheetVector .negative) =
      (-Complex.I) • sheetVector .negative := by
  funext i
  fin_cases i <;>
    simp [omegaSheet, sheetPlus, sheetMinus, sheetVector, pow_succ,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

theorem colorShift_sq_eigenvector (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (a : HexColor) :
    (colorShift ^ 2).mulVec (colorEigenvector ω a) =
      colorEigenvalue ω a ^ 2 • colorEigenvector ω a := by
  rw [pow_two, ← Matrix.mulVec_mulVec, colorShift_eigenvector ω hω,
    Matrix.mulVec_smul, colorShift_eigenvector ω hω]
  simp [pow_two, smul_smul]

theorem master_eigen_positive (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (a : HexColor) :
    masterTwelve.mulVec (sheetColorVector ω .positive a) =
      colorEigenvalue ω a ^ 2 • sheetColorVector ω .positive a := by
  rw [masterTwelve_tensor_formula, sheetColorVector,
    tensor_mulVec_pureTensor, omegaSheet_cube_eigen_positive,
    colorShift_sq_eigenvector ω hω]
  ext ⟨i, j⟩
  simp [pureTensor]
  ring

theorem master_eigen_negative (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (a : HexColor) :
    masterTwelve.mulVec (sheetColorVector ω .negative a) =
      (-Complex.I * colorEigenvalue ω a ^ 2) •
        sheetColorVector ω .negative a := by
  rw [masterTwelve_tensor_formula, sheetColorVector,
    tensor_mulVec_pureTensor, omegaSheet_cube_eigen_negative,
    colorShift_sq_eigenvector ω hω]
  ext ⟨i, j⟩
  simp [pureTensor]
  ring

theorem master_labelledVector_eigen (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : HexIndex) :
    masterTwelve.mulVec (labelledVector ω n) =
      masterEigenvalue ω n • labelledVector ω n := by
  simp only [labelledVector]
  cases h : sheetOf n
  · simpa [masterEigenvalue, h] using
      master_eigen_positive ω hω (colorOf n)
  · simpa [masterEigenvalue, h] using
      master_eigen_negative ω hω (colorOf n)

theorem masterTwelve_six_ne_one : masterTwelve ^ 6 ≠ (1 : M6C) := by
  rw [masterTwelve_six]
  intro h
  have hij := congrFun (congrFun h (1, 0)) (1, 0)
  norm_num [tensor, Matrix.kroneckerMap_apply, sheetGamma, sheetPlus,
    sheetMinus] at hij

theorem masterTwelve_four_ne_one : masterTwelve ^ 4 ≠ (1 : M6C) := by
  have hfour : masterTwelve ^ 4 =
      tensor (1 : M2C) (colorShift ^ 2) := by
    calc
      masterTwelve ^ 4 = (masterTwelve ^ 2) ^ 2 := by
        rw [← pow_mul]
      _ = sixfoldTriality ^ 2 := by rw [masterTwelve_sq]
      _ = tensor (sheetGamma ^ 2) (colorShift ^ 2) :=
        tensor_pow _ _ _
      _ = tensor (1 : M2C) (colorShift ^ 2) := by
        rw [show sheetGamma ^ 2 = (1 : M2C) by
          simpa [pow_two] using sheet_parity.1]
  intro h
  rw [hfour] at h
  have hij := congrFun (congrFun h (0, 0)) (0, 1)
  norm_num [tensor, Matrix.kroneckerMap_apply, colorShift, pow_two,
    Matrix.mul_apply, Fin.sum_univ_three] at hij

theorem masterTwelve_exact_order_certificate :
    masterTwelve ^ 12 = (1 : M6C) ∧
    masterTwelve ^ 6 ≠ (1 : M6C) ∧
    masterTwelve ^ 4 ≠ (1 : M6C) :=
  ⟨masterTwelve_twelve, masterTwelve_six_ne_one,
    masterTwelve_four_ne_one⟩

/-- The master matrix has genuine multiplicative order twelve. -/
theorem masterTwelve_orderOf : orderOf masterTwelve = 12 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) masterTwelve_twelve
  intro p hp hpdvd
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by norm_num) hpdvd
  interval_cases p
  all_goals try norm_num at hp
  all_goals try norm_num at hpdvd
  · exact masterTwelve_six_ne_one
  · exact masterTwelve_four_ne_one

end TwelveFoldSpectralBridge
end noncomputable section
