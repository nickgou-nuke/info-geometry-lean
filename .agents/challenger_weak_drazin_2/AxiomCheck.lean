import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin

noncomputable section

namespace InfoGeometry.Canonical.CampbellMeyerWeakDrazin

open InfoGeometry.Canonical

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-! ## Base Definitions from CampbellMeyerWeakDrazin.lean -/

def IsWeakDrazin {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop :=
  b * a ^ (k + 1) = a ^ k

def IsCommutingWeakDrazin {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop :=
  IsWeakDrazin a b k ∧ a * b = b * a

theorem Drazin_isWeakDrazin {R : Type*} [Ring R] {a b : R} {k : ℕ}
    (h : Drazin.IsDrazinInverse a b k) :
    IsWeakDrazin a b k := by
  unfold IsWeakDrazin
  have hcomm : Commute b a := h.comm.symm
  calc
    b * a ^ (k + 1) = a ^ (k + 1) * b := (hcomm.pow_right (k + 1)).eq
    _ = a ^ k := h.2.2

def weakA : Mat3 ℚ :=
  !![2, 0, 0;
     0, 0, 1;
     0, 0, 0]

def weakNilpotentLane : Mat3 ℚ :=
  !![0, 0, 0;
     0, 0, 1;
     0, 0, 0]

def weakRegularProjector : Mat3 ℚ :=
  !![1, 0, 0;
     0, 0, 0;
     0, 0, 0]

theorem weakNilpotentLane_sq_eq_zero :
    weakNilpotentLane ^ 2 = 0 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, weakNilpotentLane]

theorem weakA_sq_readout :
    weakA ^ 2 =
      !![4, 0, 0;
         0, 0, 0;
         0, 0, 0] := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA]; try norm_num)

lemma weakA_pow_three :
    weakA ^ 3 =
      !![8, 0, 0;
         0, 0, 0;
         0, 0, 0] := by
  change weakA ^ 2 * weakA = _
  rw [weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA]; try norm_num)

theorem weakA_cubic_eq_two_smul_square :
    weakA ^ 3 = (2 : ℚ) • weakA ^ 2 := by
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

def weakDrazinInverse : Mat3 ℚ :=
  !![1 / 2, 0, 0;
     0, 0, 0;
     0, 0, 0]

theorem weakDrazinInverse_isDrazin :
    Drazin.IsDrazinInverse weakA weakDrazinInverse 2 := by
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakDrazinInverse]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakDrazinInverse]; try norm_num)
  · rw [weakA_pow_three, weakA_sq_readout]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakDrazinInverse]; try norm_num)

theorem weakDrazinInverse_isWeak :
    IsWeakDrazin weakA weakDrazinInverse 2 :=
  Drazin_isWeakDrazin weakDrazinInverse_isDrazin

def weakWildInverse : Mat3 ℚ :=
  !![1 / 2, 3, 5;
     0, 7, 11;
     0, 13, 17]

theorem weakWildInverse_isWeak :
    IsWeakDrazin weakA weakWildInverse 2 := by
  unfold IsWeakDrazin
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakWildInverse]; try norm_num)

theorem weakWildInverse_ne_Drazin :
    weakWildInverse ≠ weakDrazinInverse := by
  intro h
  have h0 := congr_fun (congr_fun h 0) 1
  revert h0
  decide

theorem weakWildInverse_not_commuting :
    weakA * weakWildInverse ≠ weakWildInverse * weakA := by
  intro h
  have h0 := congr_fun (congr_fun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakWildInverse] at h0

def weakPolynomialInverse : Mat3 ℚ :=
  (1 / 2 : ℚ) • (1 : Mat3 ℚ)

theorem weakPolynomialInverse_isWeak :
    IsWeakDrazin weakA weakPolynomialInverse 2 := by
  unfold IsWeakDrazin
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakPolynomialInverse]; try norm_num)

theorem weakPolynomialInverse_isCommuting :
    IsCommutingWeakDrazin weakA weakPolynomialInverse 2 := by
  constructor
  · exact weakPolynomialInverse_isWeak
  · simp [weakPolynomialInverse]

def weakPolynomialInverseUnit : (Mat3 ℚ)ˣ where
  val := weakPolynomialInverse
  inv := (2 : ℚ) • (1 : Mat3 ℚ)
  val_inv := by simp [weakPolynomialInverse, smul_smul]
  inv_val := by simp [weakPolynomialInverse, smul_smul]

theorem weakPolynomialInverse_ne_Drazin :
    weakPolynomialInverse ≠ weakDrazinInverse := by
  intro h
  have h0 := congr_fun (congr_fun h 1) 1
  simp [weakPolynomialInverse, weakDrazinInverse] at h0

def weakSFp1 : ℚ :=
  Matrix.trace (weakA * (1 : Mat3 ℚ))

theorem weakSouriauFrame_formula_eq_polynomial :
    weakSFp1⁻¹ • (1 : Mat3 ℚ) = weakPolynomialInverse := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weakSFp1, weakPolynomialInverse, weakA, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

def weakProjectiveInverse : Mat3 ℚ :=
  !![1 / 2, 2, 3;
     0, 0, 5;
     0, 0, 7]

theorem weakProjectiveInverse_isWeak :
    IsWeakDrazin weakA weakProjectiveInverse 2 := by
  unfold IsWeakDrazin
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakProjectiveInverse]; try norm_num)

theorem weakProjectiveInverse_BA_readout :
    weakProjectiveInverse * weakA =
      !![1, 0, 2;
         0, 0, 0;
         0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakProjectiveInverse, weakA]; try norm_num)

theorem weakProjectiveInverse_BA_idempotent :
    (weakProjectiveInverse * weakA) * (weakProjectiveInverse * weakA) =
      weakProjectiveInverse * weakA := by
  rw [weakProjectiveInverse_BA_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

def weakCommutingInverse : Mat3 ℚ :=
  !![1 / 2, 0, 0;
     0, 3, 4;
     0, 0, 3]

theorem weakCommutingInverse_isCommuting :
    IsCommutingWeakDrazin weakA weakCommutingInverse 2 := by
  constructor
  · unfold IsWeakDrazin
    rw [weakA_pow_three, weakA_sq_readout]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakCommutingInverse]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakCommutingInverse]; try norm_num)

def weakPermutation : Mat3 ℚ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

theorem weakPermutation_sq_eq_one :
    weakPermutation * weakPermutation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakPermutation]; try norm_num)

def weakPermutationUnit : (Mat3 ℚ)ˣ where
  val := weakPermutation
  inv := weakPermutation
  val_inv := weakPermutation_sq_eq_one
  inv_val := weakPermutation_sq_eq_one

def unitConj (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) : Mat3 ℚ :=
  (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)

lemma unitConj_mul (u : (Mat3 ℚ)ˣ) (A B : Mat3 ℚ) :
    unitConj u A * unitConj u B = unitConj u (A * B) := by
  unfold unitConj
  calc
    (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * B * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
      = (u : Mat3 ℚ) * A * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * B * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      simp only [mul_assoc]
    _ = (u : Mat3 ℚ) * (A * B) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      simp only [Units.inv_mul, mul_one, mul_assoc]

lemma unitConj_pow (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) (n : ℕ) :
    (unitConj u A) ^ n = unitConj u (A ^ n) := by
  induction n with
  | zero =>
    unfold unitConj
    simp only [pow_zero]
    calc
      (1 : Mat3 ℚ) = (u : Mat3 ℚ) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := (Units.mul_inv (u : (Mat3 ℚ)ˣ)).symm
      _ = (u : Mat3 ℚ) * 1 * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by simp only [mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, unitConj_mul]

theorem unitConj_isWeakDrazin (u : (Mat3 ℚ)ˣ) (A B : Mat3 ℚ) (k : ℕ)
    (h : IsWeakDrazin A B k) :
    IsWeakDrazin (unitConj u A) (unitConj u B) k := by
  unfold IsWeakDrazin at h ⊢
  rw [unitConj_pow, unitConj_pow, unitConj_mul, h]

theorem weak_conjugated_polynomial_inverse_isWeak :
    IsWeakDrazin
      (unitConj weakPermutationUnit weakA)
      (unitConj weakPermutationUnit weakPolynomialInverse)
      2 :=
  unitConj_isWeakDrazin weakPermutationUnit weakA weakPolynomialInverse 2 weakPolynomialInverse_isWeak

/-! ========================================================================= -/
/-! ## CHALLENGER SUITE 1: STRESS-TESTING UNIVERSAL UNIT CONJUGATION THEOREM -/
/-! ========================================================================= -/

/-! ### 1.1 Non-Permutation Unit: Diagonal Scaling Unit -/

def weakScaling : Mat3 ℚ :=
  !![3, 0, 0;
     0, 5, 0;
     0, 0, 7]

def weakScalingInv : Mat3 ℚ :=
  !![1 / 3, 0, 0;
     0, 1 / 5, 0;
     0, 0, 1 / 7]

theorem weakScaling_mul_inv : weakScaling * weakScalingInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakScaling, weakScalingInv]; try norm_num)

theorem weakScaling_inv_mul : weakScalingInv * weakScaling = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakScaling, weakScalingInv]; try norm_num)

def weakScalingUnit : (Mat3 ℚ)ˣ where
  val := weakScaling
  inv := weakScalingInv
  val_inv := weakScaling_mul_inv
  inv_val := weakScaling_inv_mul

/-- Scaling conjugation preserved by general theorem. -/
theorem weak_scaling_conjugated_polynomial_isWeak :
    IsWeakDrazin
      (unitConj weakScalingUnit weakA)
      (unitConj weakScalingUnit weakPolynomialInverse)
      2 :=
  unitConj_isWeakDrazin weakScalingUnit weakA weakPolynomialInverse 2 weakPolynomialInverse_isWeak

/-- Oracle check: direct computation of scaling conjugation without using theorem. -/
theorem weak_scaling_conjugated_polynomial_isWeak_direct :
    (unitConj weakScalingUnit weakPolynomialInverse) * (unitConj weakScalingUnit weakA) ^ 3 =
    (unitConj weakScalingUnit weakA) ^ 2 := by
  rw [unitConj_pow, unitConj_pow, unitConj_mul]
  have h := weakPolynomialInverse_isWeak
  unfold IsWeakDrazin at h
  rw [h]

/-! ### 1.2 Non-Permutation Unit: Upper-Triangular Shearing Unit -/

def weakShear : Mat3 ℚ :=
  !![1, 2, -3;
     0, 1, 4;
     0, 0, 1]

def weakShearInv : Mat3 ℚ :=
  !![1, -2, 11;
     0, 1, -4;
     0, 0, 1]

theorem weakShear_mul_inv : weakShear * weakShearInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakShear, weakShearInv]; try norm_num)

theorem weakShear_inv_mul : weakShearInv * weakShear = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakShear, weakShearInv]; try norm_num)

def weakShearUnit : (Mat3 ℚ)ˣ where
  val := weakShear
  inv := weakShearInv
  val_inv := weakShear_mul_inv
  inv_val := weakShear_inv_mul

/-- Shearing conjugation on polynomial inverse. -/
theorem weak_shear_conjugated_polynomial_isWeak :
    IsWeakDrazin
      (unitConj weakShearUnit weakA)
      (unitConj weakShearUnit weakPolynomialInverse)
      2 :=
  unitConj_isWeakDrazin weakShearUnit weakA weakPolynomialInverse 2 weakPolynomialInverse_isWeak

/-- Shearing conjugation on wild inverse. -/
theorem weak_shear_conjugated_wild_isWeak :
    IsWeakDrazin
      (unitConj weakShearUnit weakA)
      (unitConj weakShearUnit weakWildInverse)
      2 :=
  unitConj_isWeakDrazin weakShearUnit weakA weakWildInverse 2 weakWildInverse_isWeak

/-- Oracle check: direct computation of shearing conjugation on wild inverse. -/
theorem weak_shear_conjugated_wild_isWeak_direct :
    (unitConj weakShearUnit weakWildInverse) * (unitConj weakShearUnit weakA) ^ 3 =
    (unitConj weakShearUnit weakA) ^ 2 := by
  rw [unitConj_pow, unitConj_pow, unitConj_mul]
  have h := weakWildInverse_isWeak
  unfold IsWeakDrazin at h
  rw [h]

/-! ### 1.3 Dense Non-Permutation Unit: Full SL₃(ℤ) Matrix -/

def weakDense : Mat3 ℚ :=
  !![1, 2, 3;
     0, 1, 4;
     5, 6, 0]

def weakDenseInv : Mat3 ℚ :=
  !![-24, 18, 5;
     20, -15, -4;
     -5, 4, 1]

theorem weakDense_mul_inv : weakDense * weakDenseInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakDense, weakDenseInv]; try norm_num)

theorem weakDense_inv_mul : weakDenseInv * weakDense = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakDense, weakDenseInv]; try norm_num)

def weakDenseUnit : (Mat3 ℚ)ˣ where
  val := weakDense
  inv := weakDenseInv
  val_inv := weakDense_mul_inv
  inv_val := weakDense_inv_mul

theorem weak_dense_conjugated_drazin_isWeak :
    IsWeakDrazin
      (unitConj weakDenseUnit weakA)
      (unitConj weakDenseUnit weakDrazinInverse)
      2 :=
  unitConj_isWeakDrazin weakDenseUnit weakA weakDrazinInverse 2 weakDrazinInverse_isWeak

/-! ### 1.4 Power Ascension and Higher Indices (k = 3, 4) -/

/-- Structural induction lemma: any weak Drazin inverse of index k is also an inverse of index k + 1. -/
lemma isWeakDrazin_succ {R : Type*} [Ring R] {a b : R} {k : ℕ}
    (h : IsWeakDrazin a b k) :
    IsWeakDrazin a b (k + 1) := by
  unfold IsWeakDrazin at h ⊢
  calc
    b * a ^ (k + 1 + 1) = b * (a ^ (k + 1) * a) := by rw [pow_succ]
    _ = (b * a ^ (k + 1)) * a := by rw [mul_assoc]
    _ = a ^ k * a := by rw [h]
    _ = a ^ (k + 1) := by rw [← pow_succ]

/-- Weak Drazin status is monotone in the index k. -/
lemma isWeakDrazin_of_le {R : Type*} [Ring R] {a b : R} {k m : ℕ}
    (hkm : k ≤ m) (h : IsWeakDrazin a b k) :
    IsWeakDrazin a b m := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hkm
  clear hkm
  induction d with
  | zero => exact h
  | succ d ih => exact isWeakDrazin_succ ih

/-- Polynomial weak inverse at power k = 3. -/
theorem weakPolynomialInverse_isWeak_three :
    IsWeakDrazin weakA weakPolynomialInverse 3 :=
  isWeakDrazin_succ weakPolynomialInverse_isWeak

/-- Polynomial weak inverse at power k = 4. -/
theorem weakPolynomialInverse_isWeak_four :
    IsWeakDrazin weakA weakPolynomialInverse 4 :=
  isWeakDrazin_succ weakPolynomialInverse_isWeak_three

/-- Unit conjugation preserves weak Drazin relation at power k = 3. -/
theorem weak_shear_conjugated_k3 :
    IsWeakDrazin (unitConj weakShearUnit weakA) (unitConj weakShearUnit weakPolynomialInverse) 3 :=
  unitConj_isWeakDrazin weakShearUnit weakA weakPolynomialInverse 3 weakPolynomialInverse_isWeak_three

/-- Unit conjugation preserves weak Drazin relation at power k = 4. -/
theorem weak_shear_conjugated_k4 :
    IsWeakDrazin (unitConj weakShearUnit weakA) (unitConj weakShearUnit weakPolynomialInverse) 4 :=
  unitConj_isWeakDrazin weakShearUnit weakA weakPolynomialInverse 4 weakPolynomialInverse_isWeak_four

/-! ### 1.5 Index Minimality Stress-Test (k = 1 strictly fails) -/

/--
The power k = 2 is minimal: at k = 1, weakPolynomialInverse fails to be a weak Drazin inverse,
proving that index reduction below the true index is mathematically false.
-/
theorem not_isWeakDrazin_k1_weakPolynomialInverse :
    ¬ IsWeakDrazin weakA weakPolynomialInverse 1 := by
  intro h
  unfold IsWeakDrazin at h
  have h0 := congr_fun (congr_fun h 1) 2
  rw [show 1 + 1 = 2 by rfl, weakA_sq_readout, pow_one] at h0
  simp [weakPolynomialInverse, weakA, Matrix.mul_apply, Fin.sum_univ_three] at h0

/-! ========================================================================= -/
/-! ## CHALLENGER SUITE 2: TWO-SIDED INVERTIBILITY OF weakPolynomialInverseUnit -/
/-! ========================================================================= -/

/-- The unit weakPolynomialInverseUnit is a genuine two-sided unit in (Mat3 ℚ)ˣ. -/
theorem weakPolynomialInverseUnit_val_inv :
    (weakPolynomialInverseUnit : Mat3 ℚ) * ((weakPolynomialInverseUnit⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) = 1 :=
  Units.mul_inv weakPolynomialInverseUnit

theorem weakPolynomialInverseUnit_inv_val :
    ((weakPolynomialInverseUnit⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (weakPolynomialInverseUnit : Mat3 ℚ) = 1 :=
  Units.inv_mul weakPolynomialInverseUnit

/-- Direct entrywise verification of right inverse in Mat3 ℚ. -/
theorem weakPolynomialInverse_mul_right_eq_one :
    weakPolynomialInverse * ((2 : ℚ) • (1 : Mat3 ℚ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakPolynomialInverse]; try norm_num)

/-- Direct entrywise verification of left inverse in Mat3 ℚ. -/
theorem weakPolynomialInverse_mul_left_eq_one :
    ((2 : ℚ) • (1 : Mat3 ℚ)) * weakPolynomialInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakPolynomialInverse]; try norm_num)

/-- Non-tautological invertibility: determinant of weakPolynomialInverse is 1/8 ≠ 0. -/
theorem weakPolynomialInverse_det_ne_zero :
    Matrix.det weakPolynomialInverse ≠ 0 := by
  simp [weakPolynomialInverse]

/-- Contrast: the standard Drazin inverse has determinant 0. -/
theorem weakDrazinInverse_det_zero :
    Matrix.det weakDrazinInverse = 0 := by
  simp [weakDrazinInverse, Matrix.det_fin_three]

/-- Contrast: the standard Drazin inverse CANNOT have any two-sided inverse in Mat3 ℚ. -/
theorem weakDrazinInverse_not_invertible :
    ¬ ∃ (B : Mat3 ℚ), weakDrazinInverse * B = 1 := by
  intro ⟨B, hB⟩
  have hdet := congr_arg Matrix.det hB
  rw [Matrix.det_mul, weakDrazinInverse_det_zero, MulZeroClass.zero_mul] at hdet
  simp at hdet


#print axioms unitConj_isWeakDrazin
#print axioms weak_scaling_conjugated_polynomial_isWeak
#print axioms weak_scaling_conjugated_polynomial_isWeak_direct
#print axioms weak_shear_conjugated_polynomial_isWeak
#print axioms weak_shear_conjugated_wild_isWeak
#print axioms weak_dense_conjugated_drazin_isWeak
#print axioms isWeakDrazin_succ
#print axioms isWeakDrazin_of_le
#print axioms weakPolynomialInverse_isWeak_three
#print axioms weakPolynomialInverse_isWeak_four
#print axioms weak_shear_conjugated_k3
#print axioms weak_shear_conjugated_k4
#print axioms not_isWeakDrazin_k1_weakPolynomialInverse
#print axioms weakPolynomialInverseUnit_val_inv
#print axioms weakPolynomialInverseUnit_inv_val
#print axioms weakPolynomialInverse_mul_right_eq_one
#print axioms weakPolynomialInverse_mul_left_eq_one
#print axioms weakPolynomialInverse_det_ne_zero
#print axioms weakDrazinInverse_det_zero
#print axioms weakDrazinInverse_not_invertible

end InfoGeometry.Canonical.CampbellMeyerWeakDrazin

