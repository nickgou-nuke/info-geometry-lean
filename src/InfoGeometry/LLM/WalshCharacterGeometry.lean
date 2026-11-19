/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Walsh characters and binary attribute kernels

The carrier is the native finite additive group `ι → ZMod 2`. The Walsh
characters are native `AddChar`s; the Walsh transform and attribute kernel
are actual real matrices. Their normalization is the cardinality of the
finite cube. The binary logarithm identity is exact two-point interpolation.

`Omega.Core.WalshFourier` independently owns integer-valued subset/Boolean-word
Fourier inversion. This file provides the native-group and real-matrix
interface; it does not duplicate that inversion theorem or assert empirical
claims about trained embeddings.
-/

noncomputable section

namespace InfoGeometry.LLM.WalshCharacterGeometry

open scoped BigOperators

/-- The nontrivial real character of the native order-two additive group. -/
def binarySign : AddChar (ZMod 2) ℝ :=
  AddChar.zmodChar 2 (ζ := (-1 : ℝ)) (by norm_num)

@[simp] theorem binarySign_one : binarySign 1 = -1 := by
  change (-1 : ℝ) ^ 1 = -1
  norm_num

theorem binarySign_sq (x : ZMod 2) : binarySign x ^ 2 = 1 := by
  fin_cases x <;> norm_num [binarySign, AddChar.zmodChar, ZMod.val]

theorem binarySign_orthogonality (a b : ZMod 2) :
    (∑ x : ZMod 2, binarySign (a * x) * binarySign (b * x)) =
      if a = b then 2 else 0 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  have ha : a = 0 ∨ a = 1 := by simpa only [hu, Finset.mem_insert,
    Finset.mem_singleton] using Finset.mem_univ a
  have hb : b = 0 ∨ b = 1 := by simpa only [hu, Finset.mem_insert,
    Finset.mem_singleton] using Finset.mem_univ b
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

variable {ι : Type*} [Fintype ι]

/-- The Walsh character indexed by a binary frequency mask. -/
def walshCharacter (a : ι → ZMod 2) : AddChar (ι → ZMod 2) ℝ where
  toFun x := ∏ i, binarySign (a i * x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

@[simp] theorem walshCharacter_apply (a x : ι → ZMod 2) :
    walshCharacter a x = ∏ i, binarySign (a i * x i) := rfl

theorem walshCharacter_symmetric (a x : ι → ZMod 2) :
    walshCharacter a x = walshCharacter x a := by
  simp only [walshCharacter_apply, mul_comm]

theorem walshCharacter_sq (a x : ι → ZMod 2) :
    walshCharacter a x ^ 2 = 1 := by
  rw [walshCharacter_apply, ← Finset.prod_pow]
  simp only [binarySign_sq, Finset.prod_const_one]

/-- Character orthogonality with the unnormalized counting measure. -/
theorem walshCharacter_orthogonality [DecidableEq ι] (a b : ι → ZMod 2) :
    (∑ x : ι → ZMod 2, walshCharacter a x * walshCharacter b x) =
      if a = b then (Fintype.card (ι → ZMod 2) : ℝ) else 0 := by
  simp only [walshCharacter_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => binarySign (a i * x) * binarySign (b i * x))]
  simp_rw [binarySign_orthogonality]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [hab]

variable [DecidableEq ι]

/-- Columns of the real Walsh matrix are the binary group characters. -/
def walshMatrix : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  fun x a => walshCharacter a x

omit [DecidableEq ι] in
theorem walshMatrix_transpose : (walshMatrix (ι := ι)).transpose = walshMatrix := by
  ext a x
  exact walshCharacter_symmetric a x

/-- The exact unnormalized matrix orthogonality law. -/
theorem walshMatrix_mul_transpose :
    walshMatrix (ι := ι) * walshMatrix.transpose =
      (Fintype.card (ι → ZMod 2) : ℝ) • (1 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, walshMatrix,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [walshCharacter_symmetric _ a, walshCharacter_symmetric _ b]
  rw [walshCharacter_orthogonality]
  split_ifs <;> simp

/-- The character matrix satisfies Mathlib's native Hadamard predicate. -/
theorem walshMatrix_isHadamard : (walshMatrix (ι := ι)).IsHadamard := by
  refine ⟨?_, ?_, ?_⟩
  · intro a x
    simp only [Unitary.mem_iff, star_trivial, walshMatrix]
    have h := walshCharacter_sq x a
    rw [pow_two] at h
    exact ⟨h, h⟩
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact walshMatrix_mul_transpose
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, walshMatrix_transpose]
    simpa only [walshMatrix_transpose] using walshMatrix_mul_transpose (ι := ι)

/-- A singleton frequency mask reads exactly one signed coordinate. -/
theorem walshCharacter_single (i : ι) (x : ι → ZMod 2) :
    walshCharacter (Pi.single i 1) x = binarySign (x i) := by
  rw [walshCharacter_apply]
  calc
    (∏ j, binarySign ((Pi.single i 1 : ι → ZMod 2) j * x j)) =
        binarySign ((Pi.single i 1 : ι → ZMod 2) i * x i) := by
      apply Finset.prod_eq_single i
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    _ = binarySign (x i) := by simp

/-- Weighted coordinate-sign interactions form a genuine matrix on the cube. -/
def attributeKernel (β : ι → ℝ) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  fun x y => ∑ i, β i * binarySign (x i) * binarySign (y i)

/-- The computed spectrum is supported on singleton frequency masks. -/
def attributeSpectrum (β : ι → ℝ) (a : ι → ZMod 2) : ℝ :=
  (Fintype.card (ι → ZMod 2) : ℝ) *
    ∑ i, if Pi.single i (1 : ZMod 2) = a then β i else 0

/-- A singleton character has its coordinate weight times the cube cardinality. -/
theorem attributeSpectrum_single (β : ι → ℝ) (i : ι) :
    attributeSpectrum β (Pi.single i 1) =
      (Fintype.card (ι → ZMod 2) : ℝ) * β i := by
  unfold attributeSpectrum
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (Pi.single j 1 : ι → ZMod 2) ≠ Pi.single i 1 := by
      intro h
      have heval := congrFun h i
      rw [Pi.single_eq_of_ne hji.symm, Pi.single_eq_same] at heval
      exact zero_ne_one heval
    simp [hne]
  · simp

/-- All nonsingleton character modes are annihilated by the attribute kernel. -/
theorem attributeSpectrum_eq_zero_of_not_singleton (β : ι → ℝ) (a : ι → ZMod 2)
    (ha : ∀ i, (Pi.single i 1 : ι → ZMod 2) ≠ a) :
    attributeSpectrum β a = 0 := by
  simp [attributeSpectrum, ha]

/-- Every Walsh character is an eigenvector of the actual attribute matrix. -/
theorem attributeKernel_mulVec_character (β : ι → ℝ) (a : ι → ZMod 2) :
    (attributeKernel β).mulVec (walshCharacter a) =
      attributeSpectrum β a • (walshCharacter a : (ι → ZMod 2) → ℝ) := by
  funext x
  change (∑ y, (∑ i, β i * binarySign (x i) * binarySign (y i)) *
    walshCharacter a y) = attributeSpectrum β a * walshCharacter a x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ y, β i * binarySign (x i) * binarySign (y i) * walshCharacter a y) =
        ∑ i, β i * binarySign (x i) *
          (∑ y, walshCharacter (Pi.single i 1) y * walshCharacter a y) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [walshCharacter_single, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ i, β i * binarySign (x i) *
        (if Pi.single i (1 : ZMod 2) = a then
          (Fintype.card (ι → ZMod 2) : ℝ) else 0) := by
      simp_rw [walshCharacter_orthogonality]
    _ = attributeSpectrum β a * walshCharacter a x := by
      simp only [attributeSpectrum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : Pi.single i (1 : ZMod 2) = a
      · subst a
        simp only [ite_true, walshCharacter_single]
        ring
      · simp [hi]

/-- Full matrix diagonalization, with eigenvalues derived from the coordinates. -/
theorem attributeKernel_mul_walshMatrix (β : ι → ℝ) :
    attributeKernel β * walshMatrix =
      walshMatrix * Matrix.diagonal (attributeSpectrum β) := by
  ext x a
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simpa only [walshMatrix, Matrix.mulVec_apply_eq_sum, Pi.smul_apply,
    smul_eq_mul, mul_comm] using congrFun (attributeKernel_mulVec_character β a) x

/-- The unnormalized Walsh congruence is the cardinality times the spectral diagonal. -/
theorem walshMatrix_transpose_mul_attributeKernel_mul (β : ι → ℝ) :
    walshMatrix.transpose * attributeKernel β * walshMatrix =
      (Fintype.card (ι → ZMod 2) : ℝ) • Matrix.diagonal (attributeSpectrum β) := by
  rw [Matrix.mul_assoc, attributeKernel_mul_walshMatrix, ← Matrix.mul_assoc]
  have horth : (walshMatrix (ι := ι)).transpose * walshMatrix =
      (Fintype.card (ι → ZMod 2) : ℝ) • (1 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ) := by
    simpa only [walshMatrix_transpose] using walshMatrix_mul_transpose (ι := ι)
  rw [horth, Matrix.smul_mul, Matrix.one_mul]

/-- Exact interpolation of a logarithm on the two signs. -/
theorem log_one_add_mul_of_sq_eq_one {s z : ℝ}
    (hs : |s| < 1) (hz : z ^ 2 = 1) :
    Real.log (1 + s * z) =
      Real.log (1 - s ^ 2) / 2 +
        z * Real.log ((1 + s) / (1 - s)) / 2 := by
  have hslo : -1 < s := (abs_lt.mp hs).1
  have hshi : s < 1 := (abs_lt.mp hs).2
  have hp : 0 < 1 + s := by linarith
  have hm : 0 < 1 - s := by linarith
  have hprod : Real.log (1 - s ^ 2) = Real.log (1 + s) + Real.log (1 - s) := by
    rw [show 1 - s ^ 2 = (1 + s) * (1 - s) by ring]
    exact Real.log_mul hp.ne' hm.ne'
  rw [hprod, Real.log_div hp.ne' hm.ne']
  rcases sq_eq_one_iff.mp hz with rfl | rfl
  · simp only [mul_one, one_mul]
    ring
  · simp only [mul_neg_one, neg_one_mul, ← sub_eq_add_neg]
    ring

/-- The real matrix of additive binary log interactions. -/
def binaryLogKernel (s : ι → ℝ) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℝ :=
  fun x y => ∑ i, Real.log (1 + s i * binarySign (x i) * binarySign (y i))

omit [DecidableEq ι] in
/-- Binary logarithms give a constant mode plus the coordinate-sign kernel;
the exact coefficients retain their logarithmic dependence on the parameters. -/
theorem binaryLogKernel_eq_constant_add_attributeKernel (s : ι → ℝ)
    (hs : ∀ i, |s i| < 1) :
    binaryLogKernel s =
      Matrix.of (fun (_ _ : ι → ZMod 2) => ∑ i, Real.log (1 - s i ^ 2) / 2) +
        attributeKernel (fun i => Real.log ((1 + s i) / (1 - s i)) / 2) := by
  ext x y
  change (∑ i, Real.log (1 + s i * binarySign (x i) * binarySign (y i))) =
    (∑ i, Real.log (1 - s i ^ 2) / 2) +
      ∑ i, Real.log ((1 + s i) / (1 - s i)) / 2 * binarySign (x i) * binarySign (y i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hz : (binarySign (x i) * binarySign (y i)) ^ 2 = 1 := by
    rw [mul_pow, binarySign_sq, binarySign_sq, one_mul]
  calc
    Real.log (1 + s i * binarySign (x i) * binarySign (y i)) =
        Real.log (1 + s i * (binarySign (x i) * binarySign (y i))) := by
      congr 1
      ring
    _ = Real.log (1 - s i ^ 2) / 2 +
        (binarySign (x i) * binarySign (y i)) *
          Real.log ((1 + s i) / (1 - s i)) / 2 :=
      log_one_add_mul_of_sq_eq_one (hs i) hz
    _ = Real.log (1 - s i ^ 2) / 2 +
        Real.log ((1 + s i) / (1 - s i)) / 2 * binarySign (x i) * binarySign (y i) := by
      ring

end InfoGeometry.LLM.WalshCharacterGeometry
