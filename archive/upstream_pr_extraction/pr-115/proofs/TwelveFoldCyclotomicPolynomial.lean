import proofs.TwelveFoldCharacteristicPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic

/-!
# Explicit twelfth cyclotomic arithmetic

This module implements the twelvefold cyclotomic polynomial framework,
identifying the exact primitive-twelve channels of the master operator.
-/

noncomputable section
namespace TwelveFoldCyclotomicPolynomial

open Polynomial TwoSheetThreeColorWeyl TwelveFoldSheetColorOmega
open SixStateCharacteristicPolynomial TwelveFoldSpectralBridge
open TwelveFoldCharacteristicPolynomial

lemma cyclotomic1_eq : cyclotomic 1 ℂ = X - 1 := cyclotomic_one ℂ
lemma cyclotomic2_eq : cyclotomic 2 ℂ = X + 1 := cyclotomic_two ℂ
lemma cyclotomic3_eq : cyclotomic 3 ℂ = X ^ 2 + X + 1 := cyclotomic_three ℂ
lemma cyclotomic4_eq : cyclotomic 4 ℂ = X ^ 2 + 1 := by
  have h : 4 = 2 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℂ, expand_eq_comp_X_pow, cyclotomic2_eq]
  simp

-- 1. Exact factorization of the twelvefold closure

theorem cyclotomic12_explicit : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  have h1 : 12 = 6 * 2 := by norm_num
  rw [h1, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ, expand_eq_comp_X_pow, cyclotomic_six]
  simp
  ring

theorem X12_sub_one_factorization :
    X ^ 12 - 1 =
      cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 12 ℤ := by
  have h := prod_cyclotomic_eq_X_pow_sub_one (n := 12) (by decide) ℤ
  rw [← h]
  have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by rfl
  rw [hdiv]
  simp
  ring

-- 2. Critical theorem boundary

theorem minpoly_masterTwelve_dvd :
    minpoly ℂ masterTwelve ∣ X ^ 12 - 1 := by
  apply minpoly.dvd
  simp only [aeval_sub, aeval_X_pow, aeval_one, sub_eq_zero]
  exact masterTwelve_twelve

-- 3. Characteristic and minimal polynomial

theorem charpoly_masterTwelve (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    masterTwelve.charpoly = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) :=
  TwelveFoldCharacteristicPolynomial.masterTwelve_charpoly ω hω

-- 4. Polynomial bridge to T = W^2

lemma cyclotomic12_eq_comp : cyclotomic 12 ℂ = (cyclotomic 6 ℂ).comp (X ^ 2) := by
  have h1 : 12 = 6 * 2 := by norm_num
  rw [h1, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℂ, expand_eq_comp_X_pow]

theorem cyclotomic12_eval_master_eq_cyclotomic6_eval_triality :
    aeval masterTwelve (cyclotomic 12 ℂ) =
      aeval sixfoldTriality (cyclotomic 6 ℂ) := by
  rw [cyclotomic12_eq_comp, aeval_comp, aeval_X_pow, masterTwelve_sq]

theorem primitiveTwelveKernel :
    LinearMap.ker (Matrix.toLin' (aeval masterTwelve (cyclotomic 12 ℂ))) =
      LinearMap.ker (Matrix.toLin' (aeval sixfoldTriality (cyclotomic 6 ℂ))) := by
  rw [cyclotomic12_eval_master_eq_cyclotomic6_eval_triality]

-- 5. Spectral filters

theorem sheetProjector_cyclotomic :
    (1 / 2 : ℂ) • aeval sheetGamma (cyclotomic 2 ℂ) = sheetPlus ∧
    -(1 / 2 : ℂ) • aeval sheetGamma (cyclotomic 1 ℂ) = sheetMinus ∧
    aeval omegaSheet (cyclotomic 4 ℂ) = (2 : ℂ) • sheetPlus := by
  constructor
  · rw [cyclotomic2_eq]
    simp [aeval_add, aeval_X, aeval_one, sheetPlus, sheetMinus, sheetGamma]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> norm_num
  constructor
  · rw [cyclotomic1_eq]
    simp [aeval_sub, aeval_X, aeval_one, sheetPlus, sheetMinus, sheetGamma]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> norm_num
  · rw [cyclotomic4_eq]
    simp [aeval_add, aeval_X_pow, aeval_one, sheetPlus, omegaSheet, sheetMinus]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two] <;> norm_num

theorem colorInvariantProjector_cyclotomic :
    (1 / 3 : ℂ) • aeval colorShift (cyclotomic 3 ℂ) =
      (1 / 3 : ℂ) • (1 + colorShift + colorShift ^ 2) := by
  rw [cyclotomic3_eq]
  simp [aeval_add, aeval_X_pow, aeval_X, aeval_one, add_assoc, add_comm]
  abel

def primitiveTwelveProjector : M6C :=
    tensor sheetMinus (1 - (1 / 3 : ℂ) • (1 + colorShift + colorShift ^ 2))

lemma tensor_sub_right (A : M2C) (B C : M3C) :
    tensor A (B - C) = tensor A B - tensor A C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tensor, Matrix.kroneckerMap, Matrix.sub_apply] <;> ring

theorem primitiveTwelveProjector_eq :
    primitiveTwelveProjector =
      tensor sheetMinus (1 : M3C) * (1 - tensor (1 : M2C) ((1 / 3 : ℂ) • (1 + colorShift + colorShift ^ 2))) := by
  rw [mul_sub, mul_one]
  unfold primitiveTwelveProjector
  have ht : tensor sheetMinus (1 : M3C) * tensor (1 : M2C) ((1 / 3 : ℂ) • (1 + colorShift + colorShift ^ 2)) = tensor (sheetMinus * 1) (1 * ((1 / 3 : ℂ) • (1 + colorShift + colorShift ^ 2))) := by
    apply tensor_mul
  rw [ht, mul_one, one_mul]
  rw [tensor_sub_right]

end TwelveFoldCyclotomicPolynomial
end noncomputable section
