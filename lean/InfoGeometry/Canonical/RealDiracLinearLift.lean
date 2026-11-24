/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealPauliPfaffianKernel
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# The faithful real Dirac lift and its alternating spinor form

The existing real Dirac vector is packaged as a native linear map. Its
Clifford square and polarization retain the existing `(-+++)` convention,
opposite to the timelike-positive scalar interval.

For the explicitly specified alternating form with matrix `timeGamma`,
the Dirac pullback is the interval times the form. Null vectors therefore
have pairwise isotropic spinor images. This is a statement about this form,
not an inference of unspecified isotropy from square-zero alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDiracLinearLift

open scoped Matrix
open InfoGeometry.Canonical.RealPauliPfaffianKernel

/-- The existing Dirac vector as a real linear map on four coordinates. -/
def diracLift : (Fin 4 → ℝ) →ₗ[ℝ] Matrix4 where
  toFun v := diracVector (v 0) (v 1) (v 2) (v 3)
  map_add' := by
    intro u v
    simp only [Pi.add_apply, diracVector, neg_add]
    rw [← pauli_add, mul_add]
  map_smul' := by
    intro r v
    have hP :
        pauli (r * v 0) (-(r * v 1)) (-(r * v 2)) (-(r * v 3)) =
          r • pauli (v 0) (-v 1) (-v 2) (-v 3) := by
      simp only [pauli, smul_add, smul_smul, mul_neg]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, diracVector]
    rw [hP, mul_smul_comm]

@[simp] theorem diracLift_apply (v : Fin 4 → ℝ) :
    diracLift v = diracVector (v 0) (v 1) (v 2) (v 3) := rfl

/-- The lift preserves all four coordinates, not merely the interval. -/
theorem diracLift_injective : Function.Injective diracLift := by
  intro u v h
  have hx := congrArg (fun M : Matrix4 => M 0 0) h
  have hy := congrArg (fun M : Matrix4 => M 0 1) h
  have hp := congrArg (fun M : Matrix4 => M 0 2) h
  have hm := congrArg (fun M : Matrix4 => M 2 0) h
  simp [diracLift_apply, diracVector, pauli_explicit, timeGamma] at hx hy hp hm
  funext i
  fin_cases i
  · change u 0 = v 0
    linarith only [hp, hm]
  · exact hx
  · exact hy
  · change u 3 = v 3
    linarith only [hp, hm]

theorem diracLift_eq_zero_iff (v : Fin 4 → ℝ) :
    diracLift v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply diracLift_injective
    exact h.trans (map_zero diracLift).symm
  · rintro rfl
    exact map_zero diracLift

/-- The full real Clifford polarization on the faithful linear image. -/
theorem diracLift_anticomm (u v : Fin 4 → ℝ) :
    diracLift u * diracLift v + diracLift v * diracLift u =
      (-2 * (u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3)) •
        (1 : Matrix4) :=
  diracVector_anticomm _ _ _ _ _ _ _ _

theorem diracLift_sq (v : Fin 4 → ℝ) :
    diracLift v * diracLift v =
      (-intervalSq (v 0) (v 1) (v 2) (v 3)) • (1 : Matrix4) :=
  diracVector_sq _ _ _ _

/-- Null coordinates are exactly the square-zero Dirac matrices. -/
theorem diracLift_sq_eq_zero_iff (v : Fin 4 → ℝ) :
    diracLift v * diracLift v = 0 ↔
      intervalSq (v 0) (v 1) (v 2) (v 3) = 0 := by
  rw [diracLift_sq]
  constructor
  · intro h
    have he := congrArg (fun M : Matrix4 => M 0 0) h
    simpa using he
  · intro h
    simp [h]

/-- Signed trace polarization recovers the timelike-positive pairing. -/
theorem diracLift_trace_mul (u v : Fin 4 → ℝ) :
    -Matrix.trace (diracLift u * diracLift v) / 4 =
      u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3 := by
  have h := congrArg Matrix.trace (diracLift_anticomm u v)
  rw [Matrix.trace_add, Matrix.trace_mul_comm (diracLift v) (diracLift u)] at h
  norm_num [Matrix.trace_smul] at h
  simp only [diracLift_apply]
  linarith only [h]

/-- The native induced endomorphism sends its image into its kernel on null input. -/
theorem diracLift_range_le_ker (v : Fin 4 → ℝ)
    (hv : intervalSq (v 0) (v 1) (v 2) (v 3) = 0) :
    LinearMap.range (Matrix.toLin' (diracLift v)) ≤
      LinearMap.ker (Matrix.toLin' (diracLift v)) := by
  apply LinearMap.range_le_ker_iff.mpr
  rw [← Matrix.toLin'_mul, (diracLift_sq_eq_zero_iff v).mpr hv, map_zero]

/-- The time generator specifies an actual alternating spinor bilinear form. -/
theorem timeGamma_isAlt : (Matrix.toBilin' timeGamma).IsAlt := by
  intro u
  have h : u 0 * u 2 - u 1 * u 3 - u 2 * u 0 + u 3 * u 1 = (0 : ℝ) := by
    ring
  simpa [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec, timeGamma,
    Fin.sum_univ_four, sub_eq_add_neg] using h

/-- The matrix congruence underlying the exact spinor-form pullback. -/
theorem diracLift_transpose_timeGamma_mul (v : Fin 4 → ℝ) :
    (diracLift v).transpose * timeGamma * diracLift v =
      intervalSq (v 0) (v 1) (v 2) (v 3) • timeGamma := by
  have hGT : timeGamma.transpose = -timeGamma := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [timeGamma]
  simp only [diracLift_apply, diracVector, Matrix.transpose_mul, pauli_transpose, hGT]
  calc
    pauli (v 0) (-v 1) (-v 2) (-v 3) * (-timeGamma) * timeGamma *
        (timeGamma * pauli (v 0) (-v 1) (-v 2) (-v 3)) =
        pauli (v 0) (-v 1) (-v 2) (-v 3) * ((-timeGamma) * timeGamma) *
          (timeGamma * pauli (v 0) (-v 1) (-v 2) (-v 3)) := by
      simp only [mul_assoc]
    _ = pauli (v 0) (-v 1) (-v 2) (-v 3) * timeGamma *
        pauli (v 0) (-v 1) (-v 2) (-v 3) := by
      rw [neg_mul, timeGamma_sq, neg_neg]
      simp only [mul_one, mul_assoc]
    _ = (timeGamma * pauli (v 0) (v 1) (v 2) (v 3)) *
        pauli (v 0) (-v 1) (-v 2) (-v 3) := by
      rw [← timeGamma_mul_pauli (v 0) (v 1) (v 2) (v 3)]
    _ = intervalSq (v 0) (v 1) (v 2) (v 3) • timeGamma := by
      rw [mul_assoc, pauli_mul_cosolder, mul_smul_comm, mul_one]

/-- Native bilinear pullback of the specified spinor form. -/
theorem diracLift_bilin_pullback (v : Fin 4 → ℝ) :
    (Matrix.toBilin' timeGamma).comp
        (Matrix.toLin' (diracLift v)) (Matrix.toLin' (diracLift v)) =
      intervalSq (v 0) (v 1) (v 2) (v 3) • Matrix.toBilin' timeGamma := by
  rw [Matrix.toBilin'_comp, diracLift_transpose_timeGamma_mul, map_smul]

/-- Every pair in the null Dirac image is orthogonal for the specified form. -/
theorem diracLift_range_isotropic (v : Fin 4 → ℝ)
    (hv : intervalSq (v 0) (v 1) (v 2) (v 3) = 0) :
    LinearMap.range (Matrix.toLin' (diracLift v)) ≤
      (LinearMap.range (Matrix.toLin' (diracLift v))).orthogonalBilin
        (Matrix.toBilin' timeGamma) := by
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_orthogonalBilin]
  rintro _ ⟨x, rfl⟩
  change ((Matrix.toBilin' timeGamma).comp
    (Matrix.toLin' (diracLift v)) (Matrix.toLin' (diracLift v))) x y = 0
  rw [diracLift_bilin_pullback, hv, zero_smul]
  simp only [LinearMap.zero_apply]

end InfoGeometry.Canonical.RealDiracLinearLift
