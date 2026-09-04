import InfoGeometry.Analysis.BipolarCriticalWindowsVortex
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Two-port scattering and transfer blocks for critical windows

This file separates ordinary unitary scattering from indefinite-metric transfer
matrices.

* `scatteringBlock r t` is the canonical `SU(2)`-form two-port block
  `[[r,-conj t],[t,conj r]]`; normalization is `|r|²+|t|²=1`.
* `hyperbolicTransfer α` is determinant one and preserves the signature matrix
  `J = diag(1,-1)`.

No resonance, bound-state, Josephson, or spectral-zero claim follows merely from
zero transmission.  No literal equality `SU(1,1) = SL(2,R)` is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoPortScattering

open InfoGeometry.Analysis.BipolarCriticalWindowsVortex
open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Canonical two-port unitary-form scattering block. -/
def scatteringBlock (r t : ℂ) : M2C :=
  !![r, -Complex.conj t;
     t, Complex.conj r]

/-- Flux normalization for the two amplitudes. -/
def ScatteringNormalized (r t : ℂ) : Prop :=
  Complex.normSq r + Complex.normSq t = 1

/-- Determinant of the scattering block is the total amplitude norm. -/
theorem det_scatteringBlock (r t : ℂ) :
    Matrix.det (scatteringBlock r t) =
      (Complex.normSq r + Complex.normSq t : ℝ) := by
  rw [Matrix.det_fin_two]
  simp [scatteringBlock, Complex.normSq_apply]
  ring

/-- A normalized scattering block has determinant one. -/
theorem det_scatteringBlock_eq_one {r t : ℂ} (h : ScatteringNormalized r t) :
    Matrix.det (scatteringBlock r t) = 1 := by
  rw [det_scatteringBlock, h]
  norm_num

/-- Exact unitary identity for the canonical scattering block. -/
theorem scatteringBlock_conjTranspose_mul (r t : ℂ) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t =
      (Complex.normSq r + Complex.normSq t : ℂ) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scatteringBlock, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.normSq_apply] <;> ring

/-- Normalization implies ordinary unitarity. -/
theorem scatteringBlock_unitary {r t : ℂ} (h : ScatteringNormalized r t) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t = 1 := by
  rw [scatteringBlock_conjTranspose_mul, h]
  simp

/-- Reflection amplitude in the left incoming channel. -/
def reflectionAmplitude (r t : ℂ) : ℂ := scatteringBlock r t 0 0

/-- Transmission amplitude from left to right. -/
def transmissionAmplitude (r t : ℂ) : ℂ := scatteringBlock r t 1 0

@[simp] theorem reflectionAmplitude_eq (r t : ℂ) : reflectionAmplitude r t = r := rfl
@[simp] theorem transmissionAmplitude_eq (r t : ℂ) : transmissionAmplitude r t = t := rfl

/-- Vanishing transmission in a normalized two-port block forces unit reflection
probability; no bound-state conclusion is inferred. -/
theorem perfect_reflection_of_zero_transmission
    {r t : ℂ} (h : ScatteringNormalized r t) (ht : t = 0) :
    Complex.normSq r = 1 := by
  rw [ScatteringNormalized, ht] at h
  simpa using h

/-- A scattering datum attached to one critical-line window. -/
structure WindowScattering where
  window : CriticalWindow
  r : ℂ
  t : ℂ
  normalized : ScatteringNormalized r t

namespace WindowScattering

/-- Matrix of the window scattering datum. -/
def matrix (W : WindowScattering) : M2C := scatteringBlock W.r W.t

/-- Every window scattering matrix is unitary. -/
theorem matrix_unitary (W : WindowScattering) : W.matrixᴴ * W.matrix = 1 := by
  exact scatteringBlock_unitary W.normalized

/-- Every window scattering matrix has determinant one. -/
theorem matrix_det (W : WindowScattering) : Matrix.det W.matrix = 1 := by
  exact det_scatteringBlock_eq_one W.normalized

end WindowScattering

/-- Signature matrix for a transfer problem. -/
def JMetric : M2C := !![(1 : ℂ), 0; 0, -1]

/-- Indefinite-metric unitarity predicate. -/
def IsJUnitary (M : M2C) : Prop := Mᴴ * JMetric * M = JMetric

/-- Special `J`-unitary predicate: flux preservation plus determinant one. -/
def IsSpecialJUnitary (M : M2C) : Prop := IsJUnitary M ∧ Matrix.det M = 1

/-- Hyperbolic determinant-one transfer block. -/
def hyperbolicTransfer (α : ℝ) : M2C :=
  !![(Real.cosh α : ℂ), (Real.sinh α : ℂ);
     (Real.sinh α : ℂ), (Real.cosh α : ℂ)]

/-- The hyperbolic transfer block has determinant one. -/
theorem hyperbolicTransfer_det (α : ℝ) : Matrix.det (hyperbolicTransfer α) = 1 := by
  rw [Matrix.det_fin_two]
  simp [hyperbolicTransfer]
  push_cast
  exact_mod_cast Real.cosh_sq_sub_sinh_sq α

/-- The hyperbolic transfer block preserves the signature form. -/
theorem hyperbolicTransfer_junitary (α : ℝ) : IsJUnitary (hyperbolicTransfer α) := by
  unfold IsJUnitary
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicTransfer, JMetric, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] <;> push_cast <;> ring_nf
  · exact_mod_cast Real.cosh_sq_sub_sinh_sq α
  · have h := Real.cosh_sq_sub_sinh_sq α
    nlinarith

/-- Therefore the hyperbolic block is special `J`-unitary. -/
theorem hyperbolicTransfer_special (α : ℝ) :
    IsSpecialJUnitary (hyperbolicTransfer α) :=
  ⟨hyperbolicTransfer_junitary α, hyperbolicTransfer_det α⟩

/-- Compact scattering/transfer separation packet. -/
theorem scattering_transfer_packet
    {r t : ℂ} (h : ScatteringNormalized r t) (α : ℝ) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t = 1 ∧
      Matrix.det (scatteringBlock r t) = 1 ∧
      IsSpecialJUnitary (hyperbolicTransfer α) := by
  exact ⟨scatteringBlock_unitary h,
    det_scatteringBlock_eq_one h,
    hyperbolicTransfer_special α⟩

end InfoGeometry.Canonical.BipolarTwoPortScattering
