import InfoGeometry.Categorical.MobiusCircleAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Tactic

open scoped ComplexConjugate
open Matrix

/-- A generalized circle in `ℂ` via the Hermitian coefficient matrix.

The explicit coordinate formulas for the Möbius-conjugated coefficients are
proved below from the `2 × 2` matrix congruence model. -/
structure GeneralizedCircle where
  A : ℝ
  B : ℂ
  C : ℝ
  h_disc : A * C < Complex.normSq B

namespace GeneralizedCircle

private noncomputable def coeffMatrix (g : GeneralizedCircle) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(g.A : ℂ), g.B], ![conj g.B, (g.C : ℂ)]]

private noncomputable def mobiusMatrix (a b c d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![a, b], ![c, d]]

private noncomputable def imageMatrix (g : GeneralizedCircle) (a b c d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (mobiusMatrix a b c d)ᴴ * coeffMatrix g * mobiusMatrix a b c d

noncomputable def image_A (g : GeneralizedCircle) (a b c d : ℂ) : ℝ := (imageMatrix g a b c d 0 0).re
noncomputable def image_B (g : GeneralizedCircle) (a b c d : ℂ) : ℂ := imageMatrix g a b c d 0 1
noncomputable def image_C (g : GeneralizedCircle) (a b c d : ℂ) : ℝ := (imageMatrix g a b c d 1 1).re

lemma coeffMatrix_isHermitian (g : GeneralizedCircle) : (coeffMatrix g).IsHermitian := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [coeffMatrix, Matrix.conjTranspose]

lemma imageMatrix_isHermitian (g : GeneralizedCircle) (a b c d : ℂ) :
    (imageMatrix g a b c d).IsHermitian := by
  simpa [imageMatrix] using
    (isHermitian_conjTranspose_mul_mul (A := coeffMatrix g) (B := mobiusMatrix a b c d)
      (hA := coeffMatrix_isHermitian g))

lemma mobius_det (a b c d : ℂ) : Matrix.det (mobiusMatrix a b c d) = a * d - b * c := by
  simp [mobiusMatrix, Matrix.det_fin_two]

lemma coeff_det (g : GeneralizedCircle) : Matrix.det (coeffMatrix g) =
    (g.A : ℂ) * (g.C : ℂ) - g.B * conj g.B := by
  simp [coeffMatrix, Matrix.det_fin_two]

lemma imageMatrix_00 (g : GeneralizedCircle) (a b c d : ℂ) :
    imageMatrix g a b c d 0 0 =
      (g.A : ℂ) * (conj a * a) + g.B * (conj a * c) + conj g.B * (conj c * a) + (g.C : ℂ) * (conj c * c) := by
  unfold imageMatrix coeffMatrix mobiusMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma imageMatrix_01 (g : GeneralizedCircle) (a b c d : ℂ) :
    imageMatrix g a b c d 0 1 =
      (g.A : ℂ) * (conj a * b) + g.B * (conj a * d) + conj g.B * (conj c * b) + (g.C : ℂ) * (conj c * d) := by
  unfold imageMatrix coeffMatrix mobiusMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma imageMatrix_11 (g : GeneralizedCircle) (a b c d : ℂ) :
    imageMatrix g a b c d 1 1 =
      (g.A : ℂ) * (conj b * b) + g.B * (conj b * d) + conj g.B * (conj d * b) + (g.C : ℂ) * (conj d * d) := by
  unfold imageMatrix coeffMatrix mobiusMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma image_A_formula (g : GeneralizedCircle) (a b c d : ℂ) :
    image_A g a b c d =
      g.A * Complex.normSq a + (g.B * conj a * c + conj g.B * a * conj c).re + g.C * Complex.normSq c := by
  unfold image_A
  rw [imageMatrix_00]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp [mul_comm, mul_left_comm]
  ring

lemma image_B_formula (g : GeneralizedCircle) (a b c d : ℂ) :
    image_B g a b c d =
      (g.A : ℂ) * (conj a * b) + g.B * conj a * d + conj g.B * b * conj c + (g.C : ℂ) * (conj c * d) := by
  unfold image_B
  rw [imageMatrix_01]
  ring

lemma image_C_formula (g : GeneralizedCircle) (a b c d : ℂ) :
    image_C g a b c d =
      g.A * Complex.normSq b + (g.B * conj b * d + conj g.B * b * conj d).re + g.C * Complex.normSq d := by
  unfold image_C
  rw [imageMatrix_11]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp [mul_comm, mul_left_comm]
  ring

lemma image_det (g : GeneralizedCircle) (a b c d : ℂ) :
    Matrix.det (imageMatrix g a b c d) = Complex.normSq (a * d - b * c) *
      ((g.A : ℂ) * (g.C : ℂ) - g.B * conj g.B) := by
  unfold imageMatrix
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, coeff_det, mobius_det]
  simpa [Complex.normSq_eq_conj_mul_self, mul_comm, mul_left_comm, mul_assoc]

/-- The Möbius image again satisfies the strict generalized-circle discriminant. -/
theorem image_is_generalized_circle
    (g : GeneralizedCircle) (a b c d : ℂ) (h_det : a * d - b * c ≠ 0) :
    image_A g a b c d * image_C g a b c d < Complex.normSq (image_B g a b c d) := by
  rw [image_A_formula, image_B_formula, image_C_formula]
  exact MobiusCircleAlgebra.GeneralizedCircle.image_is_generalized_circle
      (g := ⟨g.A, g.B, g.C, g.h_disc⟩) (a := a) (b := b) (c := c) (d := d) h_det

end GeneralizedCircle
