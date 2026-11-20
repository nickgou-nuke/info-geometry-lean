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

/-- The normalized distortion changes only by the relative positive scale.
The two underlying SPD matrices are not assumed to commute. -/
theorem normalizedDistortion_rescale (X Y : SPD n)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    normalizedDistortion (X.rescale r hr) (Y.rescale s hs) =
      (r / s) • normalizedDistortion X Y := by
  let : Invertible s := invertibleOfNonzero hs.ne'
  change (s • Y.mat)⁻¹ * (r • X.mat) = (r / s) • (Y.mat⁻¹ * X.mat)
  rw [Matrix.inv_smul (A := Y.mat) s (isUnit_iff_ne_zero.mpr Y.det_ne_zero)]
  simp only [invOf_eq_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1

/-- Exact covariance rescaling of the full Burg/Stein loss. -/
theorem steinLoss_rescale (X Y : SPD n)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    steinLoss (X.rescale r hr) (Y.rescale s hs) =
      (r / s) * Matrix.trace (normalizedDistortion X Y) -
        (n : ℝ) * Real.log (r / s) -
        Real.log (Matrix.det (normalizedDistortion X Y)) - (n : ℝ) := by
  unfold steinLoss
  rw [normalizedDistortion_rescale X Y r s hr hs,
    Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin]
  rw [Real.log_mul (pow_ne_zero n (div_ne_zero hr.ne' hs.ne'))
    (normalizedDistortion_det_pos X Y).ne', Real.log_pow]
  simp only [smul_eq_mul]
  ring

/-- Scaling the first covariance is sufficient to parametrize an entire
positive ray through the original covariance. -/
theorem steinLoss_rescale_left (X Y : SPD n) (r : ℝ) (hr : 0 < r) :
    steinLoss (X.rescale r hr) Y =
      r * Matrix.trace (normalizedDistortion X Y) -
        (n : ℝ) * Real.log r -
        Real.log (Matrix.det (normalizedDistortion X Y)) - (n : ℝ) := by
  have hdist : normalizedDistortion (X.rescale r hr) Y =
      r • normalizedDistortion X Y := by
    simp only [normalizedDistortion, SPD.rescale_mat, Matrix.mul_smul]
  unfold steinLoss
  rw [hdist, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin,
    Real.log_mul (pow_ne_zero n hr.ne')
      (normalizedDistortion_det_pos X Y).ne', Real.log_pow]
  simp only [smul_eq_mul]
  ring

/-- Simultaneous positive scaling leaves the full matrix loss invariant. -/
theorem steinLoss_common_rescale (X Y : SPD n) (r : ℝ) (hr : 0 < r) :
    steinLoss (X.rescale r hr) (Y.rescale r hr) = steinLoss X Y := by
  rw [steinLoss_rescale X Y r r hr hr, div_self hr.ne', Real.log_one]
  simp [steinLoss]

/-- For determinant-one covariance shapes, scale contributes a scalar Burg
term and multiplies the complete, generally noncommuting shape trace. -/
theorem steinLoss_rescale_unimodular (X Y : SPD n)
    (hX : X.mat.det = 1) (hY : Y.mat.det = 1)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    steinLoss (X.rescale r hr) (Y.rescale s hs) =
      (n : ℝ) * burgKernel (r / s) +
        (r / s) * (Matrix.trace (normalizedDistortion X Y) - (n : ℝ)) := by
  rw [steinLoss_rescale X Y r s hr hs, normalizedDistortion_det, hX, hY]
  simp only [div_one, Real.log_one]
  unfold burgKernel
  ring

/-- Although `Y⁻¹ X` is generally nonsymmetric, its trace is positive.
The proof uses the actual positive square root of `Y⁻¹` and a full-matrix
congruence, without replacing the covariances by commuting surrogates. -/
theorem normalizedDistortion_trace_pos (X Y : SPD n) (hn : 0 < n) :
    0 < Matrix.trace (normalizedDistortion X Y) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let C : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt Y.mat⁻¹
  have hYnonneg : 0 ≤ Y.mat⁻¹ := Y.pos.inv.posSemidef.nonneg
  have hCunit : IsUnit C :=
    (CFC.isUnit_sqrt_iff Y.mat⁻¹ hYnonneg).2 Y.pos.inv.isUnit
  have hCself : Cᴴ = C := (CFC.sqrt_nonneg Y.mat⁻¹).posSemidef.isHermitian
  have hCsq : C * C = Y.mat⁻¹ := CFC.sqrt_mul_sqrt_self _ hYnonneg
  have hpos : (Cᴴ * X.mat * C).PosDef :=
    X.pos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hCunit)
  have htrace : Matrix.trace (Cᴴ * X.mat * C) =
      Matrix.trace (normalizedDistortion X Y) := by
    rw [hCself, Matrix.trace_mul_cycle, hCsq]
    rfl
  rw [← htrace]
  exact hpos.trace_pos

/-- The scalar Burg kernel vanishes precisely at equality. -/
theorem burgKernel_eq_zero_iff {x : ℝ} (hx : 0 < x) :
    burgKernel x = 0 ↔ x = 1 := by
  constructor
  · intro hz
    by_contra hne
    have hlt := Real.log_lt_sub_one_of_pos hx hne
    unfold burgKernel at hz
    linarith
  · intro h
    rw [h, burgKernel_one]

/-- The ray scale `n / trace(Y⁻¹X)`, positive and uniquely optimal when `n > 0`.
The reference covariance is the full matrix `Y`. -/
noncomputable def steinRayScale (X Y : SPD n) : ℝ :=
  (n : ℝ) / Matrix.trace (normalizedDistortion X Y)

theorem steinRayScale_pos (X Y : SPD n) (hn : 0 < n) :
    0 < steinRayScale X Y :=
  div_pos (by exact_mod_cast hn) (normalizedDistortion_trace_pos X Y hn)

/-- Real arithmetic for the loss gap, used only after the matrix loss has
been evaluated through its actual trace and determinant. -/
private theorem real_log_ray_gap (d t b r : ℝ)
    (hd : 0 < d) (ht : 0 < t) (hr : 0 < r) :
    r * t - d * Real.log r - b - d -
        (d / t * t - d * Real.log (d / t) - b - d) =
      d * burgKernel (r / (d / t)) := by
  unfold burgKernel
  rw [Real.log_div hr.ne' (div_pos hd ht).ne']
  field_simp [ht.ne', hd.ne']
  ring

/-- Exact loss gap from the best scale: a scalar Burg kernel of the relative
scale, derived from the full-matrix loss. -/
theorem steinLoss_rescale_ray_gap (X Y : SPD n) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    steinLoss (X.rescale r hr) Y -
      steinLoss (X.rescale (steinRayScale X Y) (steinRayScale_pos X Y hn)) Y =
        (n : ℝ) * burgKernel (r / steinRayScale X Y) := by
  rw [steinLoss_rescale_left, steinLoss_rescale_left]
  unfold steinRayScale
  exact real_log_ray_gap (n : ℝ) (Matrix.trace (normalizedDistortion X Y))
    (Real.log (Matrix.det (normalizedDistortion X Y))) r
    (by exact_mod_cast hn) (normalizedDistortion_trace_pos X Y hn) hr

/-- The optimal scale globally minimizes the matrix loss on its positive ray. -/
theorem steinLoss_rescale_ray_min (X Y : SPD n) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    steinLoss (X.rescale (steinRayScale X Y) (steinRayScale_pos X Y hn)) Y ≤
      steinLoss (X.rescale r hr) Y := by
  apply sub_nonneg.mp
  rw [steinLoss_rescale_ray_gap X Y hn r hr]
  exact mul_nonneg (Nat.cast_nonneg n)
    (burgKernel_nonneg (div_pos hr (steinRayScale_pos X Y hn)))

/-- Equality in ray minimization characterizes the unique positive scale. -/
theorem steinLoss_rescale_ray_eq_iff (X Y : SPD n) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    steinLoss (X.rescale r hr) Y =
        steinLoss (X.rescale (steinRayScale X Y) (steinRayScale_pos X Y hn)) Y ↔
      r = steinRayScale X Y := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hm := steinRayScale_pos X Y hn
  rw [← sub_eq_zero, steinLoss_rescale_ray_gap X Y hn r hr, mul_eq_zero]
  simp only [hn0, false_or]
  rw [burgKernel_eq_zero_iff (div_pos hr hm), div_eq_one_iff_eq hm.ne']

end SPD

end InfoGeometry.Jordan
