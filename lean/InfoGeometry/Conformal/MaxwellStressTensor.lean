/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Real Maxwell stress tensor: symmetry and the dimension-dependent trace

This is the coefficient-algebra version of the real four-dimensional tensor
previously owned by `MannheimOpenDebtConstructiveClosure.maxwellStressTensor4`.
The diagonal metric has entries `ε i` satisfying `ε i * ε i = 1`; this allows
Lorentz, split, and positive signatures without imaginary coordinates.

The tensor is defined for every matrix `F`. Antisymmetry of a physical
electromagnetic field strength is not needed for the algebraic symmetry and
trace identities below. No Maxwell equation or stress-conservation theorem is
assumed or claimed by these results.
-/

noncomputable section

namespace InfoGeometry.Conformal.MaxwellStressTensor

open scoped BigOperators

variable {A ι : Type*} [CommRing A] [Algebra ℝ A]
variable [Fintype ι] [DecidableEq ι]

/-- Components of a diagonal metric. -/
def metricEntry (ε : ι → A) (i j : ι) : A :=
  if i = j then ε i else 0

omit [Algebra ℝ A] [Fintype ι] in
@[simp] theorem metricEntry_self (ε : ι → A) (i : ι) :
    metricEntry ε i i = ε i := by
  simp only [metricEntry, ite_true]

omit [Algebra ℝ A] [Fintype ι] in
theorem metricEntry_symm (ε : ι → A) (i j : ι) :
    metricEntry ε i j = metricEntry ε j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [metricEntry, hij, Ne.symm hij, ite_false]

/-- Metric contraction `F_{ij} F^{ij}` for a diagonal involutive metric. -/
def fieldSquare (ε : ι → A) (F : Matrix ι ι A) : A :=
  ∑ i, ∑ j, ε i * ε j * (F i j) ^ 2

/-- Covariant Maxwell stress tensor with its fixed `1/4` trace subtraction. -/
def tensor (ε : ι → A) (F : Matrix ι ι A) (i j : ι) : A :=
  (∑ k, ε k * F i k * F j k) -
    algebraMap ℝ A (1 / 4) * metricEntry ε i j * fieldSquare ε F

/-- The covariant tensor is symmetric, without requiring a field equation. -/
theorem tensor_symm (ε : ι → A) (F : Matrix ι ι A) (i j : ι) :
    tensor ε F i j = tensor ε F j i := by
  unfold tensor
  rw [metricEntry_symm ε i j]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Algebra ℝ A] in
/-- The contraction of a diagonal metric with its inverse counts dimensions. -/
theorem metric_self_contraction (ε : ι → A) (hε : ∀ i, ε i * ε i = 1) :
    (∑ i, ε i * metricEntry ε i i) = (Fintype.card ι : A) := by
  simp only [metricEntry_self, hε, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-- The Maxwell trace is exactly `(1 - d / 4) F²` in dimension `d`. -/
theorem metricTrace_tensor (ε : ι → A) (hε : ∀ i, ε i * ε i = 1)
    (F : Matrix ι ι A) :
    (∑ i, ε i * tensor ε F i i) =
      (1 - algebraMap ℝ A (1 / 4) * (Fintype.card ι : A)) * fieldSquare ε F := by
  have hsplit (i : ι) :
      ε i * tensor ε F i i =
        (∑ k, ε i * ε k * (F i k) ^ 2) -
          algebraMap ℝ A (1 / 4) * (ε i * metricEntry ε i i) * fieldSquare ε F := by
    unfold tensor
    rw [mul_sub]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · ring
  simp only [hsplit, Finset.sum_sub_distrib]
  change fieldSquare ε F -
      (∑ i, algebraMap ℝ A (1 / 4) * (ε i * metricEntry ε i i) * fieldSquare ε F) = _
  rw [← Finset.sum_mul, ← Finset.mul_sum, metric_self_contraction ε hε]
  ring

/-- In four dimensions the fixed one-quarter subtraction makes the metric trace vanish. -/
theorem metricTrace_tensor_fin4 (ε : Fin 4 → A)
    (hε : ∀ i, ε i * ε i = 1) (F : Matrix (Fin 4) (Fin 4) A) :
    (∑ i, ε i * tensor ε F i i) = 0 := by
  have hquarter : algebraMap ℝ A (1 / 4) * (4 : A) = 1 := by
    calc
      algebraMap ℝ A (1 / 4) * (4 : A) =
          algebraMap ℝ A ((1 / 4 : ℝ) * 4) := by
        simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  rw [metricTrace_tensor ε hε F]
  simp only [Fintype.card_fin, Nat.cast_ofNat, hquarter, sub_self, zero_mul]

/-- Both indices raised using the involutive diagonal metric. -/
def raisedTensor (ε : ι → A) (F : Matrix ι ι A) (i j : ι) : A :=
  ε i * ε j * tensor ε F i j

/-- Raising both indices preserves symmetry. -/
theorem raisedTensor_symm (ε : ι → A) (F : Matrix ι ι A) (i j : ι) :
    raisedTensor ε F i j = raisedTensor ε F j i := by
  unfold raisedTensor
  rw [tensor_symm ε F i j]
  ring

/-- The full lower-metric contraction of the raised tensor is its covariant metric trace. -/
theorem metric_contraction_raisedTensor
    (ε : ι → A) (hε : ∀ i, ε i * ε i = 1) (F : Matrix ι ι A) :
    (∑ i, ∑ j, metricEntry ε i j * raisedTensor ε F i j) =
      ∑ i, ε i * tensor ε F i i := by
  apply Finset.sum_congr rfl
  intro i _
  have hdiag :
      (∑ j, metricEntry ε i j * raisedTensor ε F i j) =
        ε i * raisedTensor ε F i i := by
    simp [metricEntry]
  rw [hdiag]
  unfold raisedTensor
  calc
    ε i * (ε i * ε i * tensor ε F i i) =
        (ε i * ε i) * (ε i * tensor ε F i i) := by ring
    _ = ε i * tensor ε F i i := by rw [hε i, one_mul]

/-- The full lower-metric contraction of the raised Maxwell tensor vanishes in four dimensions. -/
theorem metric_contraction_raisedTensor_fin4
    (ε : Fin 4 → A) (hε : ∀ i, ε i * ε i = 1)
    (F : Matrix (Fin 4) (Fin 4) A) :
    (∑ i, ∑ j, metricEntry ε i j * raisedTensor ε F i j) = 0 := by
  rw [metric_contraction_raisedTensor ε hε F, metricTrace_tensor_fin4 ε hε F]

end InfoGeometry.Conformal.MaxwellStressTensor

/-! ## Compatibility with the original real four-dimensional owner -/

namespace InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure

open scoped BigOperators

/-- Exact real 4D Maxwell tensor, now specialized from its focused coefficient-algebra owner.
The public name and component convention are preserved. -/
abbrev maxwellStressTensor4 (ε : Fin 4 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (μ ν : Fin 4) : ℝ :=
  InfoGeometry.Conformal.MaxwellStressTensor.tensor ε F μ ν

/-- Exact symmetry and metric trace zero of the existing four-dimensional Maxwell tensor. -/
theorem maxwellStressTensor4_symm_and_trace_zero
    (ε : Fin 4 → ℝ) (hε : ∀ μ : Fin 4, ε μ * ε μ = 1) (F : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ μ ν : Fin 4, maxwellStressTensor4 ε F μ ν = maxwellStressTensor4 ε F ν μ) ∧
    (∑ μ : Fin 4, ε μ * maxwellStressTensor4 ε F μ μ = 0) := by
  exact ⟨InfoGeometry.Conformal.MaxwellStressTensor.tensor_symm ε F,
    InfoGeometry.Conformal.MaxwellStressTensor.metricTrace_tensor_fin4 ε hε F⟩

end InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
