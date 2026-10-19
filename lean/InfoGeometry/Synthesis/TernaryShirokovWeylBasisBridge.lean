/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.TernaryShirokovCoefficientFlattening
import InfoGeometry.Canonical.QutritWeylOperatorBasis

set_option autoImplicit false

noncomputable section

open Matrix
open InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis
open InfoGeometry.Synthesis.TernaryShirokovCoefficientFlattening
open InfoGeometry.Canonical.QutritWeylOperatorBasis
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Topology.Parafermion

namespace InfoGeometry.Synthesis.TernaryShirokovWeylBasisBridge

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- Doubling is the inverse reindexing between Shirokov's forward shift and
    the canonical owner's reverse-cycle shift. -/
def doubleIndex (j : Fin 3) : Fin 3 := j + j

@[simp] private theorem doubleIndex_double (j : Fin 3) :
    doubleIndex (doubleIndex j) = j := by
  fin_cases j <;> rfl

def doubleIndexEquiv : Fin 3 ≃ Fin 3 where
  toFun := doubleIndex
  invFun := doubleIndex
  left_inv := by
    intro j
    fin_cases j <;> rfl
  right_inv := by
    intro j
    fin_cases j <;> rfl

/-- The two owners use opposite cyclic shift orientations. -/
theorem ternaryShiftP_eq_colorShift_sq :
    ternaryShiftP = colorShift ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ternaryShiftP, colorShift, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem ternaryShiftP_pow_eq_weylIndex (j : Fin 3) :
    ternaryShiftP ^ (j : ℕ) = colorShift ^ (doubleIndex j : ℕ) := by
  rw [ternaryShiftP_eq_colorShift_sq, ← pow_mul]
  have hmod : (2 * (j : ℕ)) % 3 = (doubleIndex j : ℕ) := by
    fin_cases j <;> rfl
  have hpow (n : ℕ) : colorShift ^ n = colorShift ^ (n % 3) :=
    pow_eq_pow_mod n colorShift_cubed
  rw [hpow, hmod]

private theorem ternaryWord_eq_reindexed_weyl (j k : Fin 3) :
    ternaryShiftP ^ (j : ℕ) * ternaryClockR omega ^ (k : ℕ) =
      weylWord (doubleIndex j) k := by
  rw [ternaryShiftP_pow_eq_weylIndex]
  rfl

/-- The explicit nine-term Shirokov formula is the finite sum over its
    coefficient indices. -/
private theorem flatten_eq_shirokov_sum (A : TernaryCoefficients) :
    flatten omega A =
      ∑ p : Fin 3 × Fin 3,
        A.coeff p.1 p.2 •
          (ternaryShiftP ^ (p.1 : ℕ) * ternaryClockR omega ^ (p.2 : ℕ)) := by
  rw [flatten_eq_existing_expansion]
  unfold ternaryMultivector
  simp [Fintype.sum_prod_type, Fin.sum_univ_three]
  abel

/-- The coefficient expansion rewritten in the canonical Weyl convention.
    The shift index is doubled to account for the reversed cycle. -/
theorem flatten_eq_weyl_sum (A : TernaryCoefficients) :
    flatten omega A =
      ∑ p : Fin 3 × Fin 3,
        A.coeff (doubleIndex p.1) p.2 • weylWord p.1 p.2 := by
  rw [flatten_eq_shirokov_sum]
  calc
    (∑ p : Fin 3 × Fin 3,
        A.coeff p.1 p.2 •
          (ternaryShiftP ^ (p.1 : ℕ) * ternaryClockR omega ^ (p.2 : ℕ))) =
        ∑ p : Fin 3 × Fin 3,
          A.coeff p.1 p.2 • weylWord (doubleIndex p.1) p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ternaryWord_eq_reindexed_weyl]
    _ = ∑ p : Fin 3 × Fin 3,
          A.coeff (doubleIndex p.1) p.2 • weylWord p.1 p.2 := by
      symm
      rw [Fintype.sum_equiv
        (doubleIndexEquiv.prodCongr (Equiv.refl (Fin 3)))
        (fun p : Fin 3 × Fin 3 =>
          A.coeff p.1 p.2 • weylWord (doubleIndex p.1) p.2)
        (fun p : Fin 3 × Fin 3 =>
          A.coeff (doubleIndex p.1) p.2 • weylWord p.1 p.2)]
      intro p
      simp [doubleIndexEquiv]

/-- Equal matrices have equal Shirokov coefficient arrays at the canonical
    primitive cube root, by independence of the existing nine Weyl words. -/
theorem flatten_injective : Function.Injective (flatten omega) := by
  intro A B hAB
  have hzero :
      ∑ p : Fin 3 × Fin 3,
        (A.coeff (doubleIndex p.1) p.2 -
          B.coeff (doubleIndex p.1) p.2) • weylWord p.1 p.2 = 0 := by
    have hsum :
        (∑ p : Fin 3 × Fin 3,
          (A.coeff (doubleIndex p.1) p.2 -
            B.coeff (doubleIndex p.1) p.2) • weylWord p.1 p.2) =
          (∑ p : Fin 3 × Fin 3,
            A.coeff (doubleIndex p.1) p.2 • weylWord p.1 p.2) -
          (∑ p : Fin 3 × Fin 3,
            B.coeff (doubleIndex p.1) p.2 • weylWord p.1 p.2) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [sub_smul]
    rw [hsum, ← flatten_eq_weyl_sum A, ← flatten_eq_weyl_sum B, hAB]
    simp
  have hcoeff :=
    (Fintype.linearIndependent_iff.mp weylWord_linearIndependent)
      (fun p : Fin 3 × Fin 3 =>
        A.coeff (doubleIndex p.1) p.2 -
          B.coeff (doubleIndex p.1) p.2) hzero
  cases A with
  | mk coeffA =>
    cases B with
    | mk coeffB =>
      apply congrArg TernaryCoefficients.mk
      funext j k
      have hp := hcoeff (doubleIndex j, k)
      simpa only [doubleIndex_double] using sub_eq_zero.mp hp

end InfoGeometry.Synthesis.TernaryShirokovWeylBasisBridge
