import InfoGeometry.Jordan.LogDet
import Mathlib.Tactic

/-!
# Burg / Stein Divergence on SPD

Classical Burg/Stein loss in trace-logdet form over the finite SPD lane.
-/

namespace InfoGeometry.Jordan

open Matrix
open scoped MatrixOrder

section SPD

variable {n : ℕ}

/-- Scalar convex Burg kernel. -/
noncomputable def burgKernel (x : ℝ) : ℝ :=
  x - Real.log x - 1

/-- Nonnegativity of the scalar Burg kernel on positive reals. -/
lemma burgKernel_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ burgKernel x := by
  unfold burgKernel
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  linarith

@[simp] lemma burgKernel_one : burgKernel 1 = 0 := by
  simp [burgKernel]

/--
Burg/Stein divergence on SPD matrices:
`tr(Y⁻¹X) - log det(Y⁻¹X) - n`.
-/
noncomputable def burgDivergence (X Y : SPD n) : ℝ :=
  Matrix.trace (normalizedDistortion X Y)
    - Real.log (Matrix.det (normalizedDistortion X Y))
    - (n : ℝ)

/-! Compatibility name for the former SPD API. -/
noncomputable def steinLoss (X Y : SPD n) : ℝ :=
  burgDivergence X Y

@[simp] lemma burgDivergence_eq_trace_minus_logdet_minus_dim (X Y : SPD n) :
    burgDivergence X Y
      = Matrix.trace (normalizedDistortion X Y)
          - Real.log (Matrix.det (normalizedDistortion X Y))
          - (n : ℝ) := rfl

@[simp] lemma burgDivergence_self (X : SPD n) :
    burgDivergence X X = 0 := by
  have hUnit : IsUnit (Matrix.det X.mat) := by
    exact isUnit_iff_ne_zero.mpr X.det_ne_zero
  have hInv :
      X.mat⁻¹ * X.mat = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact Matrix.nonsing_inv_mul (A := X.mat) hUnit
  unfold burgDivergence normalizedDistortion
  rw [hInv]
  simp

/--
Trace-logdet-minus-dimension form rewritten through the log-det barrier
`-log det`.
-/
lemma burgDivergence_eq_trace_add_barrier_diff_sub_dim (X Y : SPD n) :
    burgDivergence X Y
      = Matrix.trace (normalizedDistortion X Y)
          + logDetBarrier X - logDetBarrier Y - (n : ℝ) := by
  have hX : Matrix.det X.mat ≠ 0 := X.det_ne_zero
  have hY : Matrix.det Y.mat ≠ 0 := Y.det_ne_zero
  unfold burgDivergence logDetBarrier
  rw [normalizedDistortion_det, Real.log_div hX hY]
  ring

/-- Burg kernel applied to the determinant of the normalized distortion is nonnegative. -/
lemma burgKernel_normalizedDistortion_det_nonneg (X Y : SPD n) :
    0 ≤ burgKernel (Matrix.det (normalizedDistortion X Y)) := by
  exact burgKernel_nonneg (normalizedDistortion_det_pos X Y)

@[simp] lemma steinLoss_self (X : SPD n) :
    steinLoss X X = 0 := by
  simpa [steinLoss] using burgDivergence_self X

end SPD

end InfoGeometry.Jordan
