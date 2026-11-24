/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Clifford.KoszulFoundation
import Mathlib.Algebra.Group.Semiconj.Basic

/-!
# The negative four-generator word in the native split Clifford algebra

The ordered product of the four negative generators is an involution. Its
inner conjugation fixes the positive generators, negates the negative ones,
and exchanges the already normalized Witt generators. These are algebraic
statements in the existing `Cl44` owner.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl44BornReciprocity

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.KoszulFoundation

/-- The four negative vectors in their declared order. -/
def negativeVectors : List (Fin 8 → ℝ) :=
  [fVec 0, fVec 1, fVec 2, fVec 3]

/-- The native Clifford word implementing the algebraic Witt exchange. -/
def bornWord : Cl44 := cliffordVolumeElement splitQ44 negativeVectors

theorem bornWord_eq_product : bornWord = f 0 * f 1 * f 2 * f 3 := by
  simp [bornWord, negativeVectors, cliffordVolumeElement, f, mul_assoc]

private theorem negativeVectors_pairwise :
    negativeVectors.Pairwise (QuadraticMap.IsOrtho splitQ44) := by
  norm_num [negativeVectors, List.pairwise_cons, QuadraticMap.IsOrtho,
    splitQ44_apply, fVec]

/-- The four-negative-generator word has square one. -/
theorem bornWord_sq : bornWord * bornWord = 1 := by
  rw [bornWord, cliffordVolumeElement_sq_of_pairwise negativeVectors
    negativeVectors_pairwise]
  norm_num [negativeVectors, cliffordVolumeSquareScalar, splitQ44_apply, fVec]

private theorem f_mul_f_neg (i j : Fin 4) (hij : i ≠ j) :
    f i * f j = -(f j * f i) := by
  have horth : QuadraticMap.IsOrtho splitQ44 (fVec i) (fVec j) := by
    fin_cases i <;> fin_cases j <;>
      simp_all [QuadraticMap.IsOrtho, fVec, splitQ44_apply]
  apply eq_neg_of_add_eq_zero_left
  simpa only [f] using
    (CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
      (Q := splitQ44) (a := fVec i) (b := fVec j) horth)

/-- The even negative word commutes with every positive generator. -/
theorem bornWord_mul_e (i : Fin 4) : bornWord * e i = e i * bornWord := by
  have hj (j : Fin 4) : SemiconjBy (e i) (f j) (-f j) := by
    change e i * f j = (-f j) * e i
    rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left (e_mul_f_add_swap i j)
  have h := (((hj 0).mul_right (hj 1)).mul_right (hj 2)).mul_right (hj 3)
  have he : e i * bornWord = bornWord * e i := by
    simpa only [bornWord_eq_product, neg_mul, mul_neg, neg_neg] using h.eq
  exact he.symm

/-- Moving a negative generator through the word gives three sign changes. -/
theorem bornWord_mul_f (i : Fin 4) : bornWord * f i = -(f i * bornWord) := by
  have hj (j : Fin 4) :
      SemiconjBy (f i) (f j) (if i = j then f j else -f j) := by
    by_cases hij : i = j
    · subst j
      simp [SemiconjBy]
    · change f i * f j = (if i = j then f j else -f j) * f i
      rw [if_neg hij, neg_mul]
      exact f_mul_f_neg i j hij
  have h := (((hj 0).mul_right (hj 1)).mul_right (hj 2)).mul_right (hj 3)
  have hf : f i * bornWord = -(bornWord * f i) := by
    fin_cases i <;> simpa [bornWord_eq_product, neg_mul, mul_neg] using h.eq
  calc
    bornWord * f i = -(-(bornWord * f i)) := by simp
    _ = -(f i * bornWord) := congrArg Neg.neg hf.symm

theorem bornWord_conj_e (i : Fin 4) : bornWord * e i * bornWord = e i := by
  rw [bornWord_mul_e, mul_assoc, bornWord_sq, mul_one]

theorem bornWord_conj_f (i : Fin 4) : bornWord * f i * bornWord = -f i := by
  rw [bornWord_mul_f, neg_mul, mul_assoc, bornWord_sq, mul_one]

/-- The normalization is inherited from `Cl44Witt.aVec`. -/
theorem a_eq_half_sum (i : Fin 4) : a i = (1 / 2 : ℝ) • (e i + f i) := by
  simp [a, aVec, e, f]

/-- The normalization is inherited from `Cl44Witt.adagVec`. -/
theorem adag_eq_half_sub (i : Fin 4) : adag i = (1 / 2 : ℝ) • (e i - f i) := by
  simp [adag, adagVec, e, f]

/-- Algebraic Born exchange of the normalized primal Witt generator. -/
theorem bornWord_conj_a (i : Fin 4) : bornWord * a i * bornWord = adag i := by
  rw [a_eq_half_sum, adag_eq_half_sub, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, bornWord_conj_e, bornWord_conj_f]
  simp only [sub_eq_add_neg]

/-- Algebraic Born exchange of the normalized dual Witt generator. -/
theorem bornWord_conj_adag (i : Fin 4) : bornWord * adag i * bornWord = a i := by
  rw [adag_eq_half_sub, a_eq_half_sum, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, bornWord_conj_e, bornWord_conj_f]
  simp only [sub_neg_eq_add]

end InfoGeometry.Clifford.Cl44BornReciprocity
