/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Jordan.LogDet
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
noncomputable def steinLoss (X Y : SPD n) : ℝ :=
  Matrix.trace (normalizedDistortion X Y)
    - Real.log (Matrix.det (normalizedDistortion X Y))
    - (n : ℝ)

@[simp] lemma steinLoss_eq_trace_minus_logdet_minus_dim (X Y : SPD n) :
    steinLoss X Y
      = Matrix.trace (normalizedDistortion X Y)
          - Real.log (Matrix.det (normalizedDistortion X Y))
          - (n : ℝ) := rfl

@[simp] lemma steinLoss_self (X : SPD n) :
    steinLoss X X = 0 := by
  have hUnit : IsUnit (Matrix.det X.mat) := by
    exact isUnit_iff_ne_zero.mpr X.det_ne_zero
  have hInv :
      X.mat⁻¹ * X.mat = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact Matrix.nonsing_inv_mul (A := X.mat) hUnit
  unfold steinLoss normalizedDistortion
  rw [hInv]
  simp

/--
Trace-logdet-minus-dimension form rewritten through the log-det barrier
`-log det`.
-/
lemma steinLoss_eq_trace_add_barrier_diff_sub_dim (X Y : SPD n) :
    steinLoss X Y
      = Matrix.trace (normalizedDistortion X Y)
          + logDetBarrier X - logDetBarrier Y - (n : ℝ) := by
  have hX : Matrix.det X.mat ≠ 0 := X.det_ne_zero
  have hY : Matrix.det Y.mat ≠ 0 := Y.det_ne_zero
  unfold steinLoss logDetBarrier
  rw [normalizedDistortion_det, Real.log_div hX hY]
  ring

/-- Burg kernel applied to the determinant of the normalized distortion is nonnegative. -/
lemma burgKernel_normalizedDistortion_det_nonneg (X Y : SPD n) :
    0 ≤ burgKernel (Matrix.det (normalizedDistortion X Y)) := by
  exact burgKernel_nonneg (normalizedDistortion_det_pos X Y)

/-- Geometric-mean relative covariance scale. Its determinant-root property
requires positive dimension; the definition itself is total. -/
noncomputable def relativeScale (X Y : SPD n) : ℝ :=
  Real.exp (Real.log (Matrix.det (normalizedDistortion X Y)) / (n : ℝ))

/-- The determinant-one part of the full relative endomorphism `Y⁻¹ X`.
The product is not assumed symmetric or commuting. -/
noncomputable def relativeShape (X Y : SPD n) : Matrix (Fin n) (Fin n) ℝ :=
  (relativeScale X Y)⁻¹ • normalizedDistortion X Y

theorem relativeScale_pos (X Y : SPD n) : 0 < relativeScale X Y :=
  Real.exp_pos _

theorem log_relativeScale (X Y : SPD n) :
    Real.log (relativeScale X Y) =
      Real.log (Matrix.det (normalizedDistortion X Y)) / (n : ℝ) := by
  exact Real.log_exp _

theorem log_det_eq_dim_mul_log_relativeScale (X Y : SPD n) (hn : n ≠ 0) :
    Real.log (Matrix.det (normalizedDistortion X Y)) =
      (n : ℝ) * Real.log (relativeScale X Y) := by
  rw [log_relativeScale]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

theorem relativeScale_pow_dim (X Y : SPD n) (hn : n ≠ 0) :
    relativeScale X Y ^ n = Matrix.det (normalizedDistortion X Y) := by
  unfold relativeScale
  rw [← Real.exp_nat_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcancel : (n : ℝ) *
      (Real.log (Matrix.det (normalizedDistortion X Y)) / (n : ℝ)) =
      Real.log (Matrix.det (normalizedDistortion X Y)) := by
    field_simp
  rw [hcancel, Real.exp_log (normalizedDistortion_det_pos X Y)]

/-- The scale and normalized shape reconstruct the actual relative matrix. -/
theorem relativeScale_smul_relativeShape (X Y : SPD n) :
    relativeScale X Y • relativeShape X Y = normalizedDistortion X Y := by
  unfold relativeShape
  rw [smul_smul, mul_inv_cancel₀ (relativeScale_pos X Y).ne', one_smul]

theorem det_relativeShape (X Y : SPD n) (hn : n ≠ 0) :
    Matrix.det (relativeShape X Y) = 1 := by
  unfold relativeShape
  rw [Matrix.det_smul, Fintype.card_fin, inv_pow, relativeScale_pow_dim X Y hn]
  exact inv_mul_cancel₀ (normalizedDistortion_det_pos X Y).ne'

theorem trace_relativeShape (X Y : SPD n) :
    Matrix.trace (relativeShape X Y) =
      (relativeScale X Y)⁻¹ * Matrix.trace (normalizedDistortion X Y) := by
  simp [relativeShape, Matrix.trace_smul]

/-- Exact global scale/shape split. The shape cost retains its scale weight. -/
theorem steinLoss_scale_shape_split (X Y : SPD n) (hn : n ≠ 0) :
    steinLoss X Y =
      (n : ℝ) * burgKernel (relativeScale X Y) +
        relativeScale X Y * (Matrix.trace (relativeShape X Y) - (n : ℝ)) := by
  have htrace := congrArg Matrix.trace (relativeScale_smul_relativeShape X Y)
  simp only [Matrix.trace_smul, smul_eq_mul] at htrace
  unfold steinLoss burgKernel
  rw [log_det_eq_dim_mul_log_relativeScale X Y hn, ← htrace]
  ring

theorem steinLoss_scale_term_nonneg (X Y : SPD n) :
    0 ≤ (n : ℝ) * burgKernel (relativeScale X Y) :=
  mul_nonneg (Nat.cast_nonneg n) (burgKernel_nonneg (relativeScale_pos X Y))

/-- Equal relative determinant removes precisely the radial contribution. -/
theorem relativeScale_eq_one_of_det_eq_one (X Y : SPD n)
    (h : Matrix.det (normalizedDistortion X Y) = 1) :
    relativeScale X Y = 1 := by
  simp [relativeScale, h]

theorem relativeShape_eq_distortion_of_det_eq_one (X Y : SPD n)
    (h : Matrix.det (normalizedDistortion X Y) = 1) :
    relativeShape X Y = normalizedDistortion X Y := by
  simp [relativeShape, relativeScale_eq_one_of_det_eq_one X Y h]

theorem steinLoss_eq_trace_sub_dim_of_det_eq_one (X Y : SPD n)
    (h : Matrix.det (normalizedDistortion X Y) = 1) :
    steinLoss X Y = Matrix.trace (normalizedDistortion X Y) - (n : ℝ) := by
  simp [steinLoss, h]

end SPD

end InfoGeometry.Jordan
