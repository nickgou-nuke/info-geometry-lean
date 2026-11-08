import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Finite Madelung phase rotation

This file supplies the phase half of the finite covariance/Majorana picture.
The covariance/polarization half is owned by
`FiniteCovarianceMajoranaBlock`; here the phase is represented by the standard
real rotation matrix.  No operator polar-decomposition or density-matrix
vectorization theorem is asserted.
-/

open Matrix

namespace InfoGeometry.Krein.FiniteMadelungPhaseRotation

noncomputable def phaseRotation (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ]

theorem phaseRotation_transpose_mul (φ : ℝ) :
    (phaseRotation φ).transpose * phaseRotation φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf
    nlinarith [Real.sin_sq_add_cos_sq φ]
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf
    nlinarith [Real.sin_sq_add_cos_sq φ]

theorem phaseRotation_mul_transpose (φ : ℝ) :
    phaseRotation φ * (phaseRotation φ).transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  · simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ]
    nlinarith [Real.sin_sq_add_cos_sq φ]

theorem phaseRotation_add (φ ψ : ℝ) :
    phaseRotation φ * phaseRotation ψ = phaseRotation (φ + ψ) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [phaseRotation, Matrix.mul_apply, Fin.sum_univ_succ,
      Real.sin_add, Real.cos_add] <;> ring

theorem phaseRotation_zero :
    phaseRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseRotation]

/-- Reversing the real phase is transposition of the rotation matrix. -/
theorem phaseRotation_neg (φ : ℝ) :
    phaseRotation (-φ) = (phaseRotation φ).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseRotation, Real.sin_neg, Real.cos_neg]

/-- The negative phase is a right inverse of the finite rotation. -/
theorem phaseRotation_mul_neg (φ : ℝ) :
    phaseRotation φ * phaseRotation (-φ) = 1 := by
  rw [phaseRotation_add φ (-φ), add_neg_cancel, phaseRotation_zero]

/-- The negative phase is a left inverse of the finite rotation. -/
theorem phaseRotation_neg_mul (φ : ℝ) :
    phaseRotation (-φ) * phaseRotation φ = 1 := by
  rw [phaseRotation_add (-φ) φ, neg_add_cancel, phaseRotation_zero]

end InfoGeometry.Krein.FiniteMadelungPhaseRotation
