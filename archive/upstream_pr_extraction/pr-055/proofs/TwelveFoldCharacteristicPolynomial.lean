import proofs.TwelveFoldSpectralBridge
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Characteristic and minimal polynomials of the twelvefold master operator

The six labelled vectors already form a basis of the six-state carrier.  In
that basis the master operator is diagonal, so no `6 × 6` determinant
expansion is needed.
-/

noncomputable section
namespace TwelveFoldCharacteristicPolynomial

open Polynomial
open TwoSheetThreeColorWeyl TwelveFoldSheetColorOmega
open HexagonalSixRootTiling SixStateSpectralBridge
open SixStateCharacteristicPolynomial TwelveFoldSpectralBridge

abbrev State := SixStateSpectralBridge.State

def masterEnd : Module.End ℂ State := masterTwelve.mulVecLin

def finTwoHexSheet : Fin 2 ≃ HexSheet where
  toFun i := if i = 0 then .positive else .negative
  invFun s := match s with | .positive => 0 | .negative => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv s := by cases s <;> rfl

theorem labelled_master_eigenbasis (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : HexIndex) :
    masterEnd (labelledSpectralBasis ω hω n) =
      masterEigenvalue ω n • labelledSpectralBasis ω hω n := by
  simpa [masterEnd, Matrix.mulVecLin_apply] using
    master_labelledVector_eigen ω hω n

theorem master_toMatrix_spectralBasis (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    LinearMap.toMatrix (labelledSpectralBasis ω hω)
        (labelledSpectralBasis ω hω) masterEnd =
      Matrix.diagonal (masterEigenvalue ω) := by
  ext i j
  rw [LinearMap.toMatrix_apply, labelledSpectralBasis_apply]
  change ((labelledSpectralBasis ω hω).repr
      (masterTwelve.mulVec (labelledVector ω j))) i = _
  rw [master_labelledVector_eigen ω hω]
  have hrepr :
      ((labelledSpectralBasis ω hω).repr (labelledVector ω j)) i =
        if j = i then 1 else 0 := by
    simpa only [labelledSpectralBasis_apply] using
      (labelledSpectralBasis ω hω).repr_self_apply j i
  rw [map_smul]
  change masterEigenvalue ω j *
      ((labelledSpectralBasis ω hω).repr (labelledVector ω j)) i = _
  rw [hrepr]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij, Ne.symm hij]

theorem masterEnd_charpoly_eq_product (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    masterEnd.charpoly =
      ∏ n : HexIndex, (X - C (masterEigenvalue ω n)) := by
  rw [← LinearMap.charpoly_toMatrix masterEnd (labelledSpectralBasis ω hω),
    master_toMatrix_spectralBasis ω hω, Matrix.charpoly_diagonal]

@[simp] theorem masterEigenvalue_positiveVertex (ω : ℂ) (a : HexColor) :
    masterEigenvalue ω (positiveVertex a) = colorEigenvalue ω a ^ 2 := by
  change (match (sheetColorEquiv (sheetColorEquiv.symm (.positive, a))).1 with
    | .positive => colorEigenvalue ω
        (sheetColorEquiv (sheetColorEquiv.symm (.positive, a))).2 ^ 2
    | .negative => -Complex.I * colorEigenvalue ω
        (sheetColorEquiv (sheetColorEquiv.symm (.positive, a))).2 ^ 2) = _
  rw [Equiv.apply_symm_apply]

@[simp] theorem masterEigenvalue_negativeVertex (ω : ℂ) (a : HexColor) :
    masterEigenvalue ω (negativeVertex a) =
      -Complex.I * colorEigenvalue ω a ^ 2 := by
  change (match (sheetColorEquiv (sheetColorEquiv.symm (.negative, a))).1 with
    | .positive => colorEigenvalue ω
        (sheetColorEquiv (sheetColorEquiv.symm (.negative, a))).2 ^ 2
    | .negative => -Complex.I * colorEigenvalue ω
        (sheetColorEquiv (sheetColorEquiv.symm (.negative, a))).2 ^ 2) = _
  rw [Equiv.apply_symm_apply]

theorem positive_master_factor (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    (∏ a : HexColor,
      (X - C (masterEigenvalue ω (positiveVertex a)))) = X ^ 3 - 1 := by
  rw [← (ZMod.finEquiv 3).toEquiv.prod_comp]
  rw [Fin.prod_univ_three]
  norm_num [masterEigenvalue_positiveVertex, colorEigenvalue]
  rw [show (ω ^ 2) ^ 2 = ω by
    calc
      (ω ^ 2) ^ 2 = ω * ω ^ 3 := by ring
      _ = ω := by rw [TwoSheetThreeColorWeyl.omega_cube ω hω, mul_one]]
  have h20 : (2 : HexColor) ≠ 0 := by decide
  have h21 : (2 : HexColor) ≠ 1 := by decide
  simp only [h20, h21, if_false]
  calc
    _ = (X - C 1) * (X - C (ω ^ 2)) * (X - C ω) := by
      norm_num
    _ =
        X ^ 3 - C (1 + ω + ω ^ 2) * X ^ 2 +
          C (ω ^ 2 + ω + ω ^ 3) * X - C (ω ^ 3) := by
      simp only [map_add, map_pow, map_one]
      ring
    _ = X ^ 3 - 1 := by
      have hsum : 1 + ω + ω ^ 2 = 0 :=
        TwoSheetThreeColorWeyl.omega_sum ω hω
      have hpair : ω ^ 2 + ω + ω ^ 3 = 0 := by
        rw [TwoSheetThreeColorWeyl.omega_cube ω hω]
        simpa [add_comm, add_left_comm, add_assoc] using hω
      rw [hsum, hpair, TwoSheetThreeColorWeyl.omega_cube ω hω]
      simp

theorem negative_master_factor (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    (∏ a : HexColor,
      (X - C (masterEigenvalue ω (negativeVertex a)))) =
      X ^ 3 - C Complex.I := by
  rw [← (ZMod.finEquiv 3).toEquiv.prod_comp]
  rw [Fin.prod_univ_three]
  norm_num [masterEigenvalue_negativeVertex, colorEigenvalue]
  rw [show (ω ^ 2) ^ 2 = ω by
    calc
      (ω ^ 2) ^ 2 = ω * ω ^ 3 := by ring
      _ = ω := by rw [TwoSheetThreeColorWeyl.omega_cube ω hω, mul_one]]
  have h20 : (2 : HexColor) ≠ 0 := by decide
  have h21 : (2 : HexColor) ≠ 1 := by decide
  simp only [h20, h21, if_false]
  let s : ℂ := -Complex.I
  calc
    _ = (X - C s) * (X - C (s * ω ^ 2)) * (X - C (s * ω)) := by
      simp [s]
    _ =
        X ^ 3 - C (s * (1 + ω + ω ^ 2)) * X ^ 2 +
          C (s ^ 2 * (ω ^ 2 + ω + ω ^ 3)) * X -
            C (s ^ 3 * ω ^ 3) := by
      simp only [map_add, map_mul, map_pow, map_one]
      ring
    _ = X ^ 3 - C Complex.I := by
      have hsum : 1 + ω + ω ^ 2 = 0 :=
        TwoSheetThreeColorWeyl.omega_sum ω hω
      have hpair : ω ^ 2 + ω + ω ^ 3 = 0 := by
        rw [TwoSheetThreeColorWeyl.omega_cube ω hω]
        simpa [add_comm, add_left_comm, add_assoc] using hω
      have hCI : (-C Complex.I : ℂ[X]) ^ 3 = C Complex.I := by
        rw [← map_neg, ← map_pow]
        congr 1
        rw [pow_three]
        rw [show (-Complex.I) * (-Complex.I) =
          Complex.I * Complex.I by ring, Complex.I_mul_I]
        ring
      rw [hsum, hpair, TwoSheetThreeColorWeyl.omega_cube ω hω]
      simp [s, hCI]

theorem masterEigenvalue_product_factor (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    (∏ n : HexIndex, (X - C (masterEigenvalue ω n))) =
      (X ^ 3 - 1) * (X ^ 3 - C Complex.I) := by
  rw [← sheetColorEquiv.symm.prod_comp]
  rw [Fintype.prod_prod_type]
  rw [← finTwoHexSheet.prod_comp, Fin.prod_univ_two]
  change
    (∏ a : HexColor, (X - C (masterEigenvalue ω (positiveVertex a)))) *
      (∏ a : HexColor, (X - C (masterEigenvalue ω (negativeVertex a)))) = _
  rw [positive_master_factor ω hω, negative_master_factor ω hω]

theorem masterEnd_charpoly (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    masterEnd.charpoly = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) := by
  rw [masterEnd_charpoly_eq_product ω hω,
    masterEigenvalue_product_factor ω hω]

theorem masterTwelve_charpoly (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    masterTwelve.charpoly = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) := by
  rw [← Matrix.charpoly_mulVecLin]
  exact masterEnd_charpoly ω hω

theorem colorEigenvalue_sq_injective (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (fun a : HexColor => colorEigenvalue ω a ^ 2) := by
  intro a b hab
  apply colorEigenvalue_injective ω hω
  have hsquare := congrArg (fun z : ℂ => z ^ 2) hab
  calc
    colorEigenvalue ω a = (colorEigenvalue ω a ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc
        colorEigenvalue ω a = colorEigenvalue ω a * 1 := by ring
        _ = colorEigenvalue ω a * colorEigenvalue ω a ^ 3 := by
          rw [colorEigenvalue_cube ω hω a]
        _ = colorEigenvalue ω a ^ 4 := by ring
    _ = (colorEigenvalue ω b ^ 2) ^ 2 := hsquare
    _ = colorEigenvalue ω b := by
      rw [← pow_mul]
      calc
        colorEigenvalue ω b ^ 4 =
            colorEigenvalue ω b * colorEigenvalue ω b ^ 3 := by ring
        _ = colorEigenvalue ω b := by
          rw [colorEigenvalue_cube ω hω b]
          ring

theorem masterEigenvalue_sheet_cube (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : HexIndex) :
    masterEigenvalue ω n ^ 3 =
      match sheetOf n with
      | .positive => 1
      | .negative => Complex.I := by
  cases hs : sheetOf n
  · simp only [masterEigenvalue, hs]
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul,
      colorEigenvalue_cube ω hω]
    norm_num
  · simp only [masterEigenvalue, hs]
    rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul,
      colorEigenvalue_cube ω hω]
    rw [show (-Complex.I) ^ 3 = Complex.I by
      rw [pow_three]
      rw [show (-Complex.I) * (-Complex.I) =
        Complex.I * Complex.I by ring, Complex.I_mul_I]
      ring]
    simp

theorem masterEigenvalue_injective (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (masterEigenvalue ω) := by
  intro n m hnm
  have hs : sheetOf n = sheetOf m := by
    have hc := congrArg (fun z : ℂ => z ^ 3) hnm
    change masterEigenvalue ω n ^ 3 = masterEigenvalue ω m ^ 3 at hc
    rw [masterEigenvalue_sheet_cube ω hω n,
      masterEigenvalue_sheet_cube ω hω m] at hc
    cases hn : sheetOf n <;> cases hm : sheetOf m
    · rfl
    · exfalso
      rw [hn, hm] at hc
      have him := congrArg Complex.im hc
      norm_num at him
    · exfalso
      rw [hn, hm] at hc
      have him := congrArg Complex.im hc
      norm_num at him
    · rfl
  have hc : colorOf n = colorOf m := by
    apply colorEigenvalue_sq_injective ω hω
    cases hn : sheetOf n
    · have hm : sheetOf m = .positive := hs.symm.trans hn
      simpa [masterEigenvalue, hn, hm] using hnm
    · have hcancel := congrArg (fun z : ℂ => Complex.I * z) hnm
      have hm : sheetOf m = .negative := hs.symm.trans hn
      simpa [masterEigenvalue, hn, hm, Complex.I_mul_I] using hcancel
  apply sheetColorEquiv.injective
  exact Prod.ext hs hc

theorem master_hasEigenvector (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : HexIndex) :
    masterEnd.HasEigenvector (masterEigenvalue ω n) (labelledVector ω n) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    simpa [masterEnd, Matrix.mulVecLin_apply] using
      master_labelledVector_eigen ω hω n
  · exact labelledVector_nonzero ω n

theorem masterEnd_minpoly_natDegree_ge_six (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Fintype.card HexIndex ≤ (minpoly ℂ masterEnd).natDegree := by
  by_contra hdeg
  have hzero : minpoly ℂ masterEnd = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (minpoly ℂ masterEnd) (masterEigenvalue_injective ω hω)
      (fun n => Module.End.isRoot_of_hasEigenvalue
        (Module.End.hasEigenvalue_of_hasEigenvector
          (master_hasEigenvector ω hω n)))
      (Nat.lt_of_not_ge hdeg)
  exact (minpoly.ne_zero (Algebra.IsIntegral.isIntegral masterEnd)) hzero

theorem masterEnd_minpoly (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    minpoly ℂ masterEnd = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) := by
  have hdeg : masterEnd.charpoly.natDegree ≤
      (minpoly ℂ masterEnd).natDegree := by
    rw [LinearMap.charpoly_natDegree,
      ← SixStateCharacteristicPolynomial.hexIndex_card_eq_state_finrank]
    exact masterEnd_minpoly_natDegree_ge_six ω hω
  have heq : masterEnd.charpoly = minpoly ℂ masterEnd :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral masterEnd))
      (LinearMap.charpoly_monic masterEnd)
      (LinearMap.minpoly_dvd_charpoly masterEnd) hdeg
  rw [← heq]
  exact masterEnd_charpoly ω hω

theorem masterTwelve_minpoly (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    minpoly ℂ masterTwelve = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) := by
  calc
    minpoly ℂ masterTwelve = minpoly ℂ masterEnd := by
      simpa only [masterEnd] using
        (Matrix.minpoly_toLin' (R := ℂ) masterTwelve).symm
    _ = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) :=
      masterEnd_minpoly ω hω

end TwelveFoldCharacteristicPolynomial
end noncomputable section
