import InfoGeometry.Jordan.SPD
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Log-Det Barrier and Determinant Divergence on SPD

Determinant-only convex potential and relative-volume divergence for real
symmetric positive-definite matrices.
-/

namespace InfoGeometry.Jordan

open Matrix
open scoped MatrixOrder

section SPD

variable {n : ℕ}

/-- Log-determinant barrier on SPD matrices. -/
noncomputable def logDetBarrier (X : SPD n) : ℝ :=
  -Real.log (Matrix.det X.mat)

lemma SPD.det_pos (X : SPD n) : 0 < Matrix.det X.mat :=
  X.pos.det_pos

@[simp]
lemma SPD.det_ne_zero (X : SPD n) : Matrix.det X.mat ≠ 0 :=
  X.det_pos.ne'

/-- Distortion matrix `Y⁻¹X` used by determinant-relative divergence. -/
noncomputable def normalizedDistortion (X Y : SPD n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Y.mat⁻¹ * X.mat

lemma normalizedDistortion_det_pos (X Y : SPD n) :
    0 < Matrix.det (normalizedDistortion X Y) := by
  unfold normalizedDistortion
  have hYinv : 0 < Matrix.det (Y.mat⁻¹) := (Y.pos.inv).det_pos
  have hX : 0 < Matrix.det X.mat := X.det_pos
  calc
    0 < Matrix.det (Y.mat⁻¹) * Matrix.det X.mat := mul_pos hYinv hX
    _ = Matrix.det (Y.mat⁻¹ * X.mat) := by
          symm
          exact Matrix.det_mul (Y.mat⁻¹) X.mat

lemma normalizedDistortion_det (X Y : SPD n) :
    Matrix.det (normalizedDistortion X Y) = Matrix.det X.mat / Matrix.det Y.mat := by
  unfold normalizedDistortion
  calc
    Matrix.det (Y.mat⁻¹ * X.mat)
        = Matrix.det (Y.mat⁻¹) * Matrix.det X.mat := by
            exact Matrix.det_mul (Y.mat⁻¹) X.mat
    _ = (Matrix.det Y.mat)⁻¹ * Matrix.det X.mat := by
          simp [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    _ = Matrix.det X.mat / Matrix.det Y.mat := by
          simp [div_eq_mul_inv, mul_comm]

/-- Determinant-relative log-volume divergence on SPD. -/
noncomputable def logDetBregman (X Y : SPD n) : ℝ :=
  (Real.log (Matrix.det (normalizedDistortion X Y))) ^ (2 : ℕ)

lemma logDetBregman_eq_burg_form (X Y : SPD n) :
    logDetBregman X Y
      = (Real.log (Matrix.det X.mat) - Real.log (Matrix.det Y.mat)) ^ (2 : ℕ) := by
  have hX : Matrix.det X.mat ≠ 0 := X.det_ne_zero
  have hY : Matrix.det Y.mat ≠ 0 := Y.det_ne_zero
  unfold logDetBregman
  rw [normalizedDistortion_det, Real.log_div hX hY]

/-- Determinant-only nonnegativity template under positive-definiteness. -/
lemma logdet_square_nonneg_of_posDef
    (A : Matrix (Fin n) (Fin n) ℝ)
    (_hA : A.PosDef) :
    0 ≤ (Real.log (Matrix.det A)) ^ (2 : ℕ) := by
  simpa [pow_two] using mul_self_nonneg (Real.log (Matrix.det A))

/-- Nonnegativity of the determinant-relative divergence (commuting case). -/
lemma logDetBregman_nonneg_of_commute
    (X Y : SPD n)
    (_hcomm : Commute X.mat Y.mat⁻¹) :
    0 ≤ logDetBregman X Y := by
  unfold logDetBregman
  simpa [pow_two] using mul_self_nonneg (Real.log (Matrix.det (normalizedDistortion X Y)))

/-- Unconditional nonnegativity of the determinant-relative divergence on SPD. -/
lemma logDetBregman_nonneg
    (X Y : SPD n) :
    0 ≤ logDetBregman X Y := by
  unfold logDetBregman
  simpa [pow_two] using mul_self_nonneg (Real.log (Matrix.det (normalizedDistortion X Y)))

@[simp]
lemma logDetBregman_self (X : SPD n) :
    logDetBregman X X = 0 := by
  have hdet : Matrix.det X.mat ≠ 0 := X.det_ne_zero
  unfold logDetBregman
  rw [normalizedDistortion_det]
  field_simp [hdet]
  simp

end SPD

end InfoGeometry.Jordan
