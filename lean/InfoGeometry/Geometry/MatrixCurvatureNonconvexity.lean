/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.MatrixCurvatureHessian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! # A noncommutative negative direction of the actual curvature Hessian

For arbitrary matrices `X,Y`, the connection `(X,Y)` and variation `(X,-Y)`
have zero linearized curvature in that direction. Their second curvature
variation is nonzero when `X,Y` do not commute, and the actual Hessian is
strictly negative. This does not assert that the connection is a full
critical point.
-/

noncomputable section

namespace InfoGeometry.Geometry.MatrixCurvatureEnergy

open scoped Matrix Matrix.Norms.L2Operator
open InfoGeometry.Analysis.MatrixTraceQuadratic

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

theorem curvatureDifferential_opposed_eq_zero (X Y : Mat) (i j : Fin 2) :
    curvatureDifferential (fun _ : Fin 2 => (0 : Mat →L[ℝ] Mat))
      ![X, Y] i j ![X, -Y] = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [curvatureDifferential_apply]

theorem fderiv_curvatureEnergy_opposed_eq_zero (X Y : Mat) :
    fderiv ℝ (curvatureEnergy (fun _ : Fin 2 => (0 : Mat →L[ℝ] Mat)))
      ![X, Y] ![X, -Y] = 0 := by
  simp only [fderiv_curvatureEnergy_apply, curvatureDifferential_opposed_eq_zero,
    map_zero, Finset.sum_const_zero]

/-- Omitting the curvature correction would incorrectly give zero here. -/
theorem fderiv2_curvatureEnergy_opposed (X Y : Mat) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy
      (fun _ : Fin 2 => (0 : Mat →L[ℝ] Mat))))
        ![X, Y] ![X, -Y] ![X, -Y] =
      -4 * tracePair (X * Y - Y * X) (X * Y - Y * X) := by
  rw [fderiv2_curvatureEnergy_self]
  simp only [curvatureDifferential_opposed_eq_zero, map_zero, zero_add,
    Fin.sum_univ_two]
  have hxy : X * -Y - -Y * X = -(X * Y - Y * X) := by noncomm_ring
  have hyx : Y * X - X * Y = -(X * Y - Y * X) := by noncomm_ring
  have hyx' : -Y * X - X * -Y = X * Y - Y * X := by noncomm_ring
  simp only [curvatureEntry, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_apply, sub_self, zero_add, hxy, hyx, hyx', map_zero,
    map_neg, neg_apply, mul_zero, add_zero]
  ring

/-- Every noncommuting pair supplies a negative Hessian direction on the full matrix space. -/
theorem fderiv2_curvatureEnergy_opposed_neg_iff (X Y : Mat) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy
      (fun _ : Fin 2 => (0 : Mat →L[ℝ] Mat))))
        ![X, Y] ![X, -Y] ![X, -Y] < 0 ↔ ¬Commute X Y := by
  rw [fderiv2_curvatureEnergy_opposed]
  have hpos := tracePair_self_nonneg (X * Y - Y * X)
  have hzero := tracePair_self_eq_zero_iff (X * Y - Y * X)
  rw [commute_iff_eq, ← sub_eq_zero]
  constructor
  · intro h hn
    rw [hzero.mpr hn] at h
    norm_num at h
  · intro hn
    have hp : 0 < tracePair (X * Y - Y * X) (X * Y - Y * X) :=
      lt_of_le_of_ne hpos (Ne.symm (fun h => hn (hzero.mp h)))
    nlinarith

end InfoGeometry.Geometry.MatrixCurvatureEnergy
