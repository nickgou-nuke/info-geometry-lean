import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# A finite 2×2 orthogonal matrix decomposition

This module formalizes two algebraic facts suggested by the projective/Krein
intake:

* a scalar cross-ratio expression is invariant under independent nonzero
  rescalings of its two representatives;
* every real 2×2 matrix splits into scalar-diagonal, off-diagonal, and
  traceless-diagonal parts, and these three subspaces are orthogonal for the
  Frobenius inner product.

The matrix theorem is specifically two-dimensional. It does not identify this
toy splitting with a decomposition of `gl(2N, ℝ)`, a projective distance, a
Killing form, a Berezinian, or a physical entropy metric.
-/

namespace InfoGeometry.Projective.ProjectiveKreinDecomposition

open Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The scalar expression used in the proposed projective ratio. -/
noncomputable def crossRatioSq (ηuv ηuu ηvv : ℝ) : ℝ := ηuv ^ 2 / (ηuu * ηvv)

/-- Independent nonzero rescalings cancel in the scalar ratio. -/
theorem crossRatioSq_scale_invariant
    (ηuv ηuu ηvv c d : ℝ)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (huu : ηuu ≠ 0) (hvv : ηvv ≠ 0) :
    crossRatioSq (c * d * ηuv) (c ^ 2 * ηuu) (d ^ 2 * ηvv) =
      crossRatioSq ηuv ηuu ηvv := by
  unfold crossRatioSq
  have _hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have _hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  field_simp [hc, hd, huu, hvv]

/-- Scalar-diagonal direction in the real 2×2 matrix space. -/
def scaleMode (σ : ℝ) : Mat2R := !![σ, 0; 0, σ]

/-- Off-diagonal direction in the real 2×2 matrix space. -/
def chiralMode (k₁ k₂ : ℝ) : Mat2R := !![0, k₁; k₂, 0]

/-- Traceless-diagonal direction in the real 2×2 matrix space. -/
def volumeMode (a : ℝ) : Mat2R := !![a, 0; 0, -a]

/-- The Frobenius inner product `Tr(Aᵀ B)`. -/
def frobeniusInner (A B : Mat2R) : ℝ := Matrix.trace (Aᵀ * B)

theorem frobeniusInner_scale_chiral (σ k₁ k₂ : ℝ) :
    frobeniusInner (scaleMode σ) (chiralMode k₁ k₂) = 0 := by
  norm_num [frobeniusInner, scaleMode, chiralMode, Matrix.trace,
    Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]

theorem frobeniusInner_scale_volume (σ a : ℝ) :
    frobeniusInner (scaleMode σ) (volumeMode a) = 0 := by
  norm_num [frobeniusInner, scaleMode, volumeMode, Matrix.trace,
    Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]

theorem frobeniusInner_chiral_volume (k₁ k₂ a : ℝ) :
    frobeniusInner (chiralMode k₁ k₂) (volumeMode a) = 0 := by
  norm_num [frobeniusInner, chiralMode, volumeMode, Matrix.trace,
    Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]

/-- Every real 2×2 matrix is a sum of these three parts. -/
theorem decomposition (M : Mat2R) :
    M = scaleMode ((M 0 0 + M 1 1) / 2) +
      chiralMode (M 0 1) (M 1 0) +
      volumeMode ((M 0 0 - M 1 1) / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaleMode, chiralMode, volumeMode] <;> ring

/-- The Frobenius squared norm is the sum of the three component squares. -/
theorem frobenius_pythagorean (σ k₁ k₂ a : ℝ) :
    frobeniusInner
        (scaleMode σ + chiralMode k₁ k₂ + volumeMode a)
        (scaleMode σ + chiralMode k₁ k₂ + volumeMode a) =
      frobeniusInner (scaleMode σ) (scaleMode σ) +
        frobeniusInner (chiralMode k₁ k₂) (chiralMode k₁ k₂) +
        frobeniusInner (volumeMode a) (volumeMode a) := by
  (norm_num [frobeniusInner, scaleMode, chiralMode, volumeMode,
    Matrix.trace, Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]; ring)

end InfoGeometry.Projective.ProjectiveKreinDecomposition
