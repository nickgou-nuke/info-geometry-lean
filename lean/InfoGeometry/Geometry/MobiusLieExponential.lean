/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.MobiusInfinitesimal
import InfoGeometry.Canonical.MatrixDetExpTraceJacobi
import Mathlib.Tactic

/-!
# Closed-form exponential of a trace-zero `2 × 2` complex matrix

Pure-math core of Theorem 3.1 of "On Möbius Transformations as Pólya Vector
Fields from Lie Theory Viewpoint", with all interpretation language stripped.

For `X = [[a,b],[c,-a]]` we prove the trace-zero Cayley--Hamilton identity
`X^2 = (a^2 + bc) I = (-det X) I`.  Setting `ω^2 = -det X`, the exponential is

* `exp X = I + X` when `det X = 0` (parabolic);
* `exp X = cosh ω • I + (sinh ω / ω) • X` when `det X ≠ 0` (non-parabolic).

The proofs reduce to the square-zero / square-one closed forms for the matrix
exponential already available in `MatrixDetExpTraceJacobi`, after rescaling
`X` by `ω⁻¹`.  No physics vocabulary appears in the statements.
-/

noncomputable section

namespace InfoGeometry.Geometry.MobiusLieExponential

open InfoGeometry.Canonical.MatrixDetExpTraceJacobi
open InfoGeometry.Geometry

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Cayley--Hamilton for trace-zero `2 × 2` -/

/-- Square of a trace-zero `2 × 2` complex matrix is a scalar matrix:
`X^2 = (a^2 + bc) I`. -/
theorem sl2C_matrix_sq (M : sl2C) :
    M.matrix * M.matrix = (M.a ^ 2 + M.b * M.c) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2C.matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Trace-zero Cayley--Hamilton in determinant form: `X^2 = (-det X) I`. -/
theorem sl2C_matrix_sq_eq_neg_det (M : sl2C) :
    M.matrix * M.matrix = (-(M.matrix.det)) • (1 : M2C) := by
  rw [sl2C_matrix_sq, sl2C.matrix_det]
  simp

/-! ## Exponential, parabolic case -/

/-- If `det X = 0`, then `exp (t X) = I + t X` for every `t` (square-zero case). -/
theorem exp_sl2C_parabolic (M : sl2C) (hdet : M.matrix.det = 0) (t : ℂ) :
    NormedSpace.exp (t • M.matrix) = (1 : M2C) + t • M.matrix := by
  have hs : M.a ^ 2 + M.b * M.c = 0 := by
    have h := sl2C.matrix_det M
    rw [hdet] at h
    simpa using (neg_eq_zero.mp h.symm)
  have hsq : M.matrix * M.matrix = 0 := by
    rw [sl2C_matrix_sq, hs]
    simp
  simpa [matrixExpFlow] using
    (matrixExpFlow_eq_one_add_of_sq_eq_zero M.matrix hsq t)

/-- Theorem 3.1, parabolic case at `t = 1`: `exp X = I + X`. -/
theorem exp_sl2C_parabolic_one (M : sl2C) (hdet : M.matrix.det = 0) :
    NormedSpace.exp M.matrix = (1 : M2C) + M.matrix := by
  simpa using (exp_sl2C_parabolic M hdet 1)

/-! ## Exponential, non-parabolic case -/

/-- If `det X ≠ 0` and `ω^2 = -det X`, then for every `t`
`exp (t X) = cosh (t ω) I + (sinh (t ω) / ω) X`. -/
theorem exp_sl2C_nonparabolic (M : sl2C) (hdet : M.matrix.det ≠ 0) {ω : ℂ}
    (hω : ω ^ 2 = -(M.matrix.det)) (t : ℂ) :
    NormedSpace.exp (t • M.matrix) =
      Complex.cosh (t * ω) • (1 : M2C) +
        (Complex.sinh (t * ω) / ω) • M.matrix := by
  have hωne : ω ≠ 0 := by
    intro h0
    apply hdet
    have hz : -(M.matrix.det) = 0 := by simpa [h0] using hω.symm
    exact neg_eq_zero.mp hz
  let B : M2C := ω⁻¹ • M.matrix
  have hBsq : B * B = (1 : M2C) := by
    dsimp [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [sl2C_matrix_sq_eq_neg_det, smul_smul, ← hω]
    have hscalar : ω⁻¹ * ω⁻¹ * ω ^ 2 = (1 : ℂ) := by
      field_simp [hωne]
    rw [hscalar, one_smul]
  have hflow := matrixExpFlow_eq_cosh_add_sinh_of_sq_eq_one B hBsq (t * ω)
  have hL : matrixExpFlow B (t * ω) = NormedSpace.exp (t • M.matrix) := by
    simp only [matrixExpFlow]
    dsimp [B]
    congr 1
    rw [smul_smul]
    have htw : (t * ω) * ω⁻¹ = t := by field_simp [hωne]
    rw [htw]
  have hR :
      Complex.cosh (t * ω) • (1 : M2C) + Complex.sinh (t * ω) • B =
        Complex.cosh (t * ω) • (1 : M2C) +
          (Complex.sinh (t * ω) / ω) • M.matrix := by
    congr 1
    dsimp [B]
    rw [smul_smul, div_eq_mul_inv]
  calc
    NormedSpace.exp (t • M.matrix) = matrixExpFlow B (t * ω) := hL.symm
    _ = Complex.cosh (t * ω) • (1 : M2C) + Complex.sinh (t * ω) • B := hflow
    _ = Complex.cosh (t * ω) • (1 : M2C) +
          (Complex.sinh (t * ω) / ω) • M.matrix := hR

/-- Theorem 3.1, non-parabolic case at `t = 1`:
`exp X = cosh ω I + (sinh ω / ω) X` with `ω^2 = -det X`. -/
theorem exp_sl2C_nonparabolic_one (M : sl2C) (hdet : M.matrix.det ≠ 0) {ω : ℂ}
    (hω : ω ^ 2 = -(M.matrix.det)) :
    NormedSpace.exp M.matrix =
      Complex.cosh ω • (1 : M2C) + (Complex.sinh ω / ω) • M.matrix := by
  simpa using (exp_sl2C_nonparabolic M hdet hω 1)

/-- Explicit matrix entries of the non-parabolic exponential (paper eq. (8)/(9)). -/
theorem exp_sl2C_nonparabolic_entries (M : sl2C) (hdet : M.matrix.det ≠ 0) {ω : ℂ}
    (hω : ω ^ 2 = -(M.matrix.det)) :
    NormedSpace.exp M.matrix =
      !![Complex.cosh ω + (Complex.sinh ω / ω) * M.a,
           (Complex.sinh ω / ω) * M.b;
         (Complex.sinh ω / ω) * M.c,
           Complex.cosh ω - (Complex.sinh ω / ω) * M.a] := by
  rw [exp_sl2C_nonparabolic_one M hdet hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [sl2C.matrix]
    try ring

/-! ## Flow-level structure of the explicit exponential `ρ(t) = exp (t X)` -/

/-- The one-parameter exponential flow of a trace-zero matrix. -/
def sl2CExpFlow (M : sl2C) (t : ℂ) : M2C := matrixExpFlow M.matrix t

/-- The flow starts at the identity. -/
theorem sl2CExpFlow_zero (M : sl2C) : sl2CExpFlow M 0 = (1 : M2C) := by
  simp [sl2CExpFlow, matrixExpFlow]

/-- The flow is an additive one-parameter group. -/
theorem sl2CExpFlow_add (M : sl2C) (s t : ℂ) :
    sl2CExpFlow M (s + t) = sl2CExpFlow M s * sl2CExpFlow M t := by
  let A := M.matrix
  have hcomm : Commute (s • A) (t • A) :=
    ((Commute.refl A).smul_left s).smul_right t
  simpa [sl2CExpFlow, matrixExpFlow, A, add_smul] using
    (Matrix.exp_add_of_commute (s • A) (t • A) hcomm)

/-- The flow satisfies the left ODE `ρ'(t) = X ρ(t)`. -/
theorem sl2CExpFlow_hasDerivAt (M : sl2C) (t : ℂ) :
    HasDerivAt (sl2CExpFlow M) (M.matrix * sl2CExpFlow M t) t := by
  change HasDerivAt (fun z : ℂ => NormedSpace.exp (z • M.matrix))
    (M.matrix * NormedSpace.exp (t • M.matrix)) t
  exact hasDerivAt_matrixExpFlow_left M.matrix t

/-- Trace-zero forces `det ρ(t) = 1` for every `t`. -/
theorem sl2CExpFlow_det (M : sl2C) (t : ℂ) :
    Matrix.det (sl2CExpFlow M t) = 1 := by
  rw [sl2CExpFlow, det_matrixExpFlow_eq_exp_trace_mul]
  simp [Matrix.trace, sl2C.matrix]

end InfoGeometry.Geometry.MobiusLieExponential
