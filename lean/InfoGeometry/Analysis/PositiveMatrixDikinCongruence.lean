/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Analysis.PositiveMatrixDikin

/-!
# Congruence and simultaneous scaling of the native Dikin quadratic form

## Theorem contract

The first two lemmas are matrix algebra over an arbitrary commutative star ring.
They need only `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, which imports
the trace API. An invertible matrix `C` acts by `P ↦ C * P * Cᴴ` and by the same
congruence on tangent directions. No matrices are assumed to commute, and the
algebraic trace identity does not require the base point to be invertible.

The complex-matrix results reuse `PositiveMatrixDikin.traceQuadratic` and
`normalizedVariation`. Strict positivity is used to identify the normalized
trace square with the existing Dikin quadratic. Simultaneous real scaling is
proved for a nonzero scalar and an invertible base point; positive scaling on
the positive cone is a corollary. These are finite-matrix coordinate identities.

-/

noncomputable section

open Matrix

namespace Matrix

variable {α n : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

/-- Under invertible congruence, an inverse variation transforms by similarity. -/
theorem inv_mul_conjTranspose_congr
    (P H C : Matrix n n α) (hC : IsUnit C) :
    (C * P * Cᴴ)⁻¹ * (C * H * Cᴴ) =
      (Cᴴ)⁻¹ * (P⁻¹ * H) * Cᴴ := by
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC
  calc
    (C * P * Cᴴ)⁻¹ * (C * H * Cᴴ) =
        (Cᴴ)⁻¹ * P⁻¹ * (C⁻¹ * C) * H * Cᴴ := by
      simp only [Matrix.mul_inv_rev, mul_assoc]
    _ = (Cᴴ)⁻¹ * (P⁻¹ * H) * Cᴴ := by
      rw [Matrix.nonsing_inv_mul C hCdet]
      simp only [mul_one, mul_assoc]

/-- The ordered mixed inverse trace form is invariant under invertible congruence. -/
theorem trace_inv_mul_inv_mul_conjTranspose_congr
    (P K H C : Matrix n n α) (hC : IsUnit C) :
    Matrix.trace
        ((C * P * Cᴴ)⁻¹ * (C * K * Cᴴ) *
          (C * P * Cᴴ)⁻¹ * (C * H * Cᴴ)) =
      Matrix.trace (P⁻¹ * K * P⁻¹ * H) := by
  have hCstar : IsUnit Cᴴ := (Matrix.isUnit_conjTranspose C).mpr hC
  have hCstar_det : IsUnit (Cᴴ).det :=
    (Matrix.isUnit_iff_isUnit_det Cᴴ).mp hCstar
  have hcancel : Cᴴ * (Cᴴ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Cᴴ hCstar_det
  calc
    Matrix.trace
        ((C * P * Cᴴ)⁻¹ * (C * K * Cᴴ) *
          (C * P * Cᴴ)⁻¹ * (C * H * Cᴴ)) =
        Matrix.trace
          (((C * P * Cᴴ)⁻¹ * (C * K * Cᴴ)) *
            ((C * P * Cᴴ)⁻¹ * (C * H * Cᴴ))) := by
      simp only [mul_assoc]
    _ = Matrix.trace
        (((Cᴴ)⁻¹ * (P⁻¹ * K) * Cᴴ) *
          ((Cᴴ)⁻¹ * (P⁻¹ * H) * Cᴴ)) := by
      rw [inv_mul_conjTranspose_congr P K C hC,
        inv_mul_conjTranspose_congr P H C hC]
    _ = Matrix.trace
        ((Cᴴ)⁻¹ * (P⁻¹ * K) * (Cᴴ * (Cᴴ)⁻¹) * (P⁻¹ * H) * Cᴴ) := by
      simp only [mul_assoc]
    _ = Matrix.trace ((Cᴴ)⁻¹ * (P⁻¹ * K * P⁻¹ * H) * Cᴴ) := by
      rw [hcancel]
      simp only [mul_one, mul_assoc]
    _ = Matrix.trace (Cᴴ * (Cᴴ)⁻¹ * (P⁻¹ * K * P⁻¹ * H)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (P⁻¹ * K * P⁻¹ * H) := by
      rw [hcancel, one_mul]

end Matrix

namespace InfoGeometry.Analysis.PositiveMatrixDikin

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The existing Dikin trace quadratic is invariant under any invertible change of frame. -/
theorem traceQuadratic_congr (P H C : Mat) (hC : IsUnit C) :
    traceQuadratic (C * P * Cᴴ) (C * H * Cᴴ) = traceQuadratic P H := by
  simpa only [traceQuadratic, reTrace, pow_two, mul_assoc] using
    congrArg Complex.re
      (Matrix.trace_inv_mul_inv_mul_conjTranspose_congr P H H C hC)

/-- Inverse-square-root normalization has the same trace square in every invertible frame. -/
theorem normalizedVariation_trace_sq_congr {P : Mat}
    (hP : IsStrictlyPositive P) (H C : Mat) (hC : IsUnit C) :
    reTrace (normalizedVariation (C * P * Cᴴ) (C * H * Cᴴ) ^ 2) =
      reTrace (normalizedVariation P H ^ 2) := by
  have hCP : IsStrictlyPositive (C * P * Cᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (hC.isStrictlyPositive_star_right_conjugate_iff).mpr hP
  calc
    reTrace (normalizedVariation (C * P * Cᴴ) (C * H * Cᴴ) ^ 2) =
        traceQuadratic (C * P * Cᴴ) (C * H * Cᴴ) :=
      (traceQuadratic_eq_normalized hCP _).symm
    _ = traceQuadratic P H := traceQuadratic_congr P H C hC
    _ = reTrace (normalizedVariation P H ^ 2) := traceQuadratic_eq_normalized hP H

/-- Simultaneous nonzero real scaling leaves the existing Dikin quadratic unchanged. -/
theorem traceQuadratic_smul {P : Mat} (hP : IsUnit P) (H : Mat)
    (c : ℝ) (hc : c ≠ 0) :
    traceQuadratic (c • P) (c • H) = traceQuadratic P H := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hinv : (c • P)⁻¹ = c⁻¹ • P⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul P hPdet]
  have hvariation : (c • P)⁻¹ * (c • H) = P⁻¹ * H := by
    rw [hinv]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc, one_smul]
  unfold traceQuadratic
  rw [hvariation]

/-- Positive Weyl scaling preserves the native Dikin quadratic on the positive cone. -/
theorem traceQuadratic_smul_pos {P : Mat} (hP : IsStrictlyPositive P)
    (H : Mat) (c : ℝ) (hc : 0 < c) :
    traceQuadratic (c • P) (c • H) = traceQuadratic P H :=
  traceQuadratic_smul hP.isUnit H c (ne_of_gt hc)

end InfoGeometry.Analysis.PositiveMatrixDikin
