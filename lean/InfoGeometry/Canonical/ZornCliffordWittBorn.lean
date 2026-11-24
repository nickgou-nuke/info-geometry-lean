/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordSourceVolume

/-!
# Four real Witt modes and the Born exchange operator

The operators act on the existing real `DiracSpinor16` carrier.  The ordered
vector frame is `(1, q₁, ..., q₇)` from `ZornCliffordSourceVolume`; its norm
signs are `(+,+,+,+,-,-,-,-)`.  The first and last four generators give the
normalized Witt operators `½(Γ₊ + Γ₋)` and `½(Γ₊ - Γ₋)`.

The scalar polar table and the existing native Clifford lift give the CAR.
The unnormalized mixed anticommutator is `4 δ I`, whereas the normalized
mixed anticommutator is `δ I`.  The product of the four negative-square
generators is an involution whose conjugation exchanges these Witt modes.

This construction does not add another octonion multiplication, change the
source volume orientation, or assert faithfulness of the Clifford lift.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornClifford

/-- The unit followed by the seven published imaginary source vectors. -/
def sourceCliffordVector : Fin 8 → ZornMatrix ℝ :=
  ![1, sourceImaginaryVector 0, sourceImaginaryVector 1,
    sourceImaginaryVector 2, sourceImaginaryVector 3,
    sourceImaginaryVector 4, sourceImaginaryVector 5, sourceImaginaryVector 6]

private theorem sourceCliffordVector_coordinates (i : Fin 8) :
    sourceCliffordVector i =
      (![⟨1, 1, ![0, 0, 0], ![0, 0, 0]⟩,
         ⟨0, 0, ![-1, 0, 0], ![1, 0, 0]⟩,
         ⟨0, 0, ![0, -1, 0], ![0, 1, 0]⟩,
         ⟨0, 0, ![0, 0, -1], ![0, 0, 1]⟩,
         ⟨0, 0, ![1, 0, 0], ![1, 0, 0]⟩,
         ⟨0, 0, ![0, 1, 0], ![0, 1, 0]⟩,
         ⟨0, 0, ![0, 0, 1], ![0, 0, 1]⟩,
         ⟨-1, 1, ![0, 0, 0], ![0, 0, 0]⟩] : Fin 8 → ZornMatrix ℝ) i := by
  have hraw : sourceCliffordVector i =
      (![⟨1, 1, 0, 0⟩,
         ⟨-0, -0, -InfoGeometry.Algebra.ZornVec3.basis 0,
           -(-InfoGeometry.Algebra.ZornVec3.basis 0)⟩,
         ⟨-0, -0, -InfoGeometry.Algebra.ZornVec3.basis 1,
           -(-InfoGeometry.Algebra.ZornVec3.basis 1)⟩,
         ⟨-0, -0, -InfoGeometry.Algebra.ZornVec3.basis 2,
           -(-InfoGeometry.Algebra.ZornVec3.basis 2)⟩,
         ⟨0, 0, InfoGeometry.Algebra.ZornVec3.basis 0,
           InfoGeometry.Algebra.ZornVec3.basis 0⟩,
         ⟨0, 0, InfoGeometry.Algebra.ZornVec3.basis 1,
           InfoGeometry.Algebra.ZornVec3.basis 1⟩,
         ⟨0, 0, InfoGeometry.Algebra.ZornVec3.basis 2,
           InfoGeometry.Algebra.ZornVec3.basis 2⟩,
         ⟨-1, -(-1), -0, -0⟩] : Fin 8 → ZornMatrix ℝ) i := by
    fin_cases i <;> rfl
  rw [hraw]
  fin_cases i <;> ext j <;> (try fin_cases j) <;>
    norm_num [InfoGeometry.Algebra.ZornVec3.basis]

/-- The source frame has four positive and four negative norm squares. -/
theorem sourceCliffordVector_norm (i : Fin 8) :
    zornNorm (sourceCliffordVector i) = if i.val < 4 then 1 else -1 := by
  rw [sourceCliffordVector_coordinates]
  fin_cases i <;> norm_num [zornNorm_apply, zornNormFun, ZornMatrix.dot]

/-- `polar` is unhalved: a unit frame vector has polar square `±2`. -/
theorem sourceCliffordVector_polar (i j : Fin 8) :
    QuadraticMap.polar zornNorm (sourceCliffordVector i) (sourceCliffordVector j) =
      if i = j then 2 * (if i.val < 4 then (1 : ℝ) else -1) else 0 := by
  rw [sourceCliffordVector_coordinates i, sourceCliffordVector_coordinates j]
  fin_cases i <;> fin_cases j <;>
    norm_num [QuadraticMap.polar, zornNorm_apply, zornNormFun, ZornMatrix.dot]

/-- The genuine real Dirac action of a source frame vector. -/
def sourceGamma (i : Fin 8) : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  diracGammaLinear (sourceCliffordVector i)

/-- Polarization of the already constructed native Clifford action. -/
theorem diracGamma_anticommutator (x y : ZornMatrix ℝ) :
    diracGammaLinear x * diracGammaLinear y +
        diracGammaLinear y * diracGammaLinear x =
      QuadraticMap.polar zornNorm x y •
        (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using
    CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq
      (Q := zornNorm (R := ℝ)) diracGammaLinear diracGamma_sq x y

theorem sourceGamma_sq (i : Fin 8) :
    sourceGamma i * sourceGamma i =
      (if i.val < 4 then (1 : ℝ) else -1) •
        (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  simpa only [sourceGamma, sourceCliffordVector_norm,
    Algebra.algebraMap_eq_smul_one] using diracGamma_sq (sourceCliffordVector i)

/-- All eight source operators satisfy the real `(4,4)` Clifford relation. -/
theorem sourceGamma_anticommutator (i j : Fin 8) :
    sourceGamma i * sourceGamma j + sourceGamma j * sourceGamma i =
      (if i = j then 2 * (if i.val < 4 then (1 : ℝ) else -1) else 0) •
        (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  simpa only [sourceGamma, sourceCliffordVector_polar] using
    diracGamma_anticommutator (sourceCliffordVector i) (sourceCliffordVector j)

theorem sourceGamma_anticommute {i j : Fin 8} (h : i ≠ j) :
    sourceGamma i * sourceGamma j = -(sourceGamma j * sourceGamma i) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [if_neg h, zero_smul] using sourceGamma_anticommutator i j

private def positiveIndex (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩

private def negativeIndex (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

/-- The positive-square source generators. -/
def sourcePositiveGamma (i : Fin 4) : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  sourceGamma (positiveIndex i)

/-- The negative-square source generators. -/
def sourceNegativeGamma (i : Fin 4) : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  sourceGamma (negativeIndex i)

/-- Four normalized primal Witt operators on the real Dirac module. -/
def primalWitt (i : Fin 4) : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  (1 / 2 : ℝ) • (sourcePositiveGamma i + sourceNegativeGamma i)

/-- Four normalized dual Witt operators on the real Dirac module. -/
def dualWitt (i : Fin 4) : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  (1 / 2 : ℝ) • (sourcePositiveGamma i - sourceNegativeGamma i)

private theorem primalWitt_eq_gamma (i : Fin 4) :
    primalWitt i = diracGammaLinear
      ((1 / 2 : ℝ) • (sourceCliffordVector (positiveIndex i) +
        sourceCliffordVector (negativeIndex i))) := by
  simp only [map_smul, map_add, primalWitt, sourcePositiveGamma,
    sourceNegativeGamma, sourceGamma]

private theorem dualWitt_eq_gamma (i : Fin 4) :
    dualWitt i = diracGammaLinear
      ((1 / 2 : ℝ) • (sourceCliffordVector (positiveIndex i) -
        sourceCliffordVector (negativeIndex i))) := by
  simp only [map_smul, map_sub, dualWitt, sourcePositiveGamma,
    sourceNegativeGamma, sourceGamma]

/-- The primal modes mutually anticommute. -/
theorem primalWitt_anticommutator (i j : Fin 4) :
    primalWitt i * primalWitt j + primalWitt j * primalWitt i = 0 := by
  rw [primalWitt_eq_gamma i, primalWitt_eq_gamma j, diracGamma_anticommutator]
  simp only [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    sourceCliffordVector_polar, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [positiveIndex, negativeIndex]

/-- The dual modes mutually anticommute. -/
theorem dualWitt_anticommutator (i j : Fin 4) :
    dualWitt i * dualWitt j + dualWitt j * dualWitt i = 0 := by
  rw [dualWitt_eq_gamma i, dualWitt_eq_gamma j, diracGamma_anticommutator]
  simp only [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
    sourceCliffordVector_polar, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [positiveIndex, negativeIndex]

/-- The normalized mixed CAR has coefficient one. -/
theorem primalWitt_dualWitt_anticommutator (i j : Fin 4) :
    primalWitt i * dualWitt j + dualWitt j * primalWitt i =
      (if i = j then (1 : ℝ) else 0) •
        (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  rw [primalWitt_eq_gamma i, dualWitt_eq_gamma j, diracGamma_anticommutator]
  simp only [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_add_left, QuadraticMap.polar_sub_right,
    sourceCliffordVector_polar, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [positiveIndex, negativeIndex]

/-- Without the two factors of `½`, the mixed coefficient is four. -/
theorem unnormalizedWitt_anticommutator (i j : Fin 4) :
    (sourcePositiveGamma i + sourceNegativeGamma i) *
        (sourcePositiveGamma j - sourceNegativeGamma j) +
      (sourcePositiveGamma j - sourceNegativeGamma j) *
        (sourcePositiveGamma i + sourceNegativeGamma i) =
      (if i = j then (4 : ℝ) else 0) •
        (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  have hp : QuadraticMap.polar zornNorm
      (sourceCliffordVector (positiveIndex i) + sourceCliffordVector (negativeIndex i))
      (sourceCliffordVector (positiveIndex j) - sourceCliffordVector (negativeIndex j)) =
        if i = j then (4 : ℝ) else 0 := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_sub_right,
      sourceCliffordVector_polar]
    fin_cases i <;> fin_cases j <;> norm_num [positiveIndex, negativeIndex]
  have h := diracGamma_anticommutator
    (sourceCliffordVector (positiveIndex i) + sourceCliffordVector (negativeIndex i))
    (sourceCliffordVector (positiveIndex j) - sourceCliffordVector (negativeIndex j))
  rw [hp] at h
  simpa only [map_add, map_sub, sourcePositiveGamma, sourceNegativeGamma,
    sourceGamma] using h

private theorem signed_mul {A : Type*} [Ring A] [Algebra ℝ A]
    (a b x : A) (s t : ℝ)
    (ha : a * x = s • (x * a)) (hb : b * x = t • (x * b)) :
    (a * b) * x = (s * t) • (x * (a * b)) := by
  calc
    (a * b) * x = a * (b * x) := mul_assoc _ _ _
    _ = a * (t • (x * b)) := by rw [hb]
    _ = t • ((a * x) * b) := by rw [mul_smul_comm, ← mul_assoc]
    _ = t • ((s • (x * a)) * b) := by rw [ha]
    _ = (s * t) • (x * (a * b)) := by
      rw [smul_mul_assoc, smul_smul, mul_comm t s, mul_assoc]

private theorem signed_mul_four {A : Type*} [Ring A] [Algebra ℝ A]
    (a b c d x : A) (s t u v : ℝ)
    (ha : a * x = s • (x * a)) (hb : b * x = t • (x * b))
    (hc : c * x = u • (x * c)) (hd : d * x = v • (x * d)) :
    (a * b * c * d) * x = (s * t * u * v) • (x * (a * b * c * d)) :=
  signed_mul (a * b * c) d x (s * t * u) v
    (signed_mul (a * b) c x (s * t) u (signed_mul a b x s t ha hb) hc) hd

private theorem sourceGamma_signed_commute (i j : Fin 8) :
    sourceGamma i * sourceGamma j =
      (if i = j then (1 : ℝ) else -1) • (sourceGamma j * sourceGamma i) := by
  by_cases h : i = j
  · simp only [h, if_pos rfl, one_smul]
  · simpa only [if_neg h, neg_one_smul] using sourceGamma_anticommute h

/-- The four negative-square source generators, in their fixed source order. -/
def bornReciprocityOp : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  sourceGamma 4 * sourceGamma 5 * sourceGamma 6 * sourceGamma 7

/-- Four sign changes make the Born operator commute with positive generators. -/
theorem bornReciprocityOp_commutes_positive (i : Fin 4) :
    bornReciprocityOp * sourcePositiveGamma i =
      sourcePositiveGamma i * bornReciprocityOp := by
  have h := signed_mul_four (sourceGamma 4) (sourceGamma 5) (sourceGamma 6)
    (sourceGamma 7) (sourceGamma (positiveIndex i)) _ _ _ _
    (sourceGamma_signed_commute 4 (positiveIndex i))
    (sourceGamma_signed_commute 5 (positiveIndex i))
    (sourceGamma_signed_commute 6 (positiveIndex i))
    (sourceGamma_signed_commute 7 (positiveIndex i))
  fin_cases i <;>
    simpa [bornReciprocityOp, sourcePositiveGamma, positiveIndex] using h

/-- Three sign changes make the Born operator anticommute with negative generators. -/
theorem bornReciprocityOp_anticommutes_negative (i : Fin 4) :
    bornReciprocityOp * sourceNegativeGamma i =
      -(sourceNegativeGamma i * bornReciprocityOp) := by
  have h := signed_mul_four (sourceGamma 4) (sourceGamma 5) (sourceGamma 6)
    (sourceGamma 7) (sourceGamma (negativeIndex i)) _ _ _ _
    (sourceGamma_signed_commute 4 (negativeIndex i))
    (sourceGamma_signed_commute 5 (negativeIndex i))
    (sourceGamma_signed_commute 6 (negativeIndex i))
    (sourceGamma_signed_commute 7 (negativeIndex i))
  fin_cases i <;>
    simpa [bornReciprocityOp, sourceNegativeGamma, negativeIndex] using h

private theorem negative_pair_sq {A : Type*} [Ring A] (a b : A)
    (hba : b * a = -(a * b)) (ha : a * a = -1) (hb : b * b = -1) :
    (a * b) * (a * b) = -1 := by
  calc
    (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = -((a * a) * (b * b)) := by rw [hba]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [ha, hb]; simp

/-- The four-negative-generator Born operator is an involution. -/
theorem bornReciprocityOp_sq : bornReciprocityOp * bornReciprocityOp = 1 := by
  let a := sourceGamma 4 * sourceGamma 5
  let b := sourceGamma 6 * sourceGamma 7
  have h4 : sourceGamma 4 * sourceGamma 4 = -1 := by
    simpa using sourceGamma_sq 4
  have h5 : sourceGamma 5 * sourceGamma 5 = -1 := by
    simpa using sourceGamma_sq 5
  have h6 : sourceGamma 6 * sourceGamma 6 = -1 := by
    simpa using sourceGamma_sq 6
  have h7 : sourceGamma 7 * sourceGamma 7 = -1 := by
    simpa using sourceGamma_sq 7
  have ha : a * a = -1 :=
    negative_pair_sq _ _ (sourceGamma_anticommute (i := 5) (j := 4) (by decide)) h4 h5
  have hb : b * b = -1 :=
    negative_pair_sq _ _ (sourceGamma_anticommute (i := 7) (j := 6) (by decide)) h6 h7
  have ha6 : a * sourceGamma 6 = sourceGamma 6 * a := by
    simpa [a] using signed_mul (sourceGamma 4) (sourceGamma 5) (sourceGamma 6) _ _
      (sourceGamma_signed_commute 4 6) (sourceGamma_signed_commute 5 6)
  have ha7 : a * sourceGamma 7 = sourceGamma 7 * a := by
    simpa [a] using signed_mul (sourceGamma 4) (sourceGamma 5) (sourceGamma 7) _ _
      (sourceGamma_signed_commute 4 7) (sourceGamma_signed_commute 5 7)
  have hab : a * b = b * a := by
    change a * (sourceGamma 6 * sourceGamma 7) = (sourceGamma 6 * sourceGamma 7) * a
    rw [← mul_assoc, ha6, mul_assoc, ha7, ← mul_assoc]
  calc
    bornReciprocityOp * bornReciprocityOp = (a * b) * (a * b) := by
      simp only [bornReciprocityOp, a, b, mul_assoc]
    _ = a * (b * a) * b := by simp only [mul_assoc]
    _ = (a * a) * (b * b) := by rw [← hab]; simp only [mul_assoc]
    _ = 1 := by rw [ha, hb]; simp

/-- Born conjugation exchanges each normalized primal mode with its dual. -/
theorem bornReciprocityOp_primalWitt (i : Fin 4) :
    bornReciprocityOp * primalWitt i * bornReciprocityOp = dualWitt i := by
  unfold primalWitt dualWitt
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    bornReciprocityOp_commutes_positive, bornReciprocityOp_anticommutes_negative]
  simp only [neg_mul, mul_assoc, bornReciprocityOp_sq, mul_one, sub_eq_add_neg]

/-- Born conjugation also exchanges each normalized dual mode with its primal. -/
theorem bornReciprocityOp_dualWitt (i : Fin 4) :
    bornReciprocityOp * dualWitt i * bornReciprocityOp = primalWitt i := by
  unfold primalWitt dualWitt
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul,
    bornReciprocityOp_commutes_positive, bornReciprocityOp_anticommutes_negative]
  simp only [neg_mul, mul_assoc, bornReciprocityOp_sq, mul_one, sub_neg_eq_add]

end InfoGeometry.Canonical.ZornClifford

end
