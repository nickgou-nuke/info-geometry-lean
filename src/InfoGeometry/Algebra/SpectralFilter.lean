/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Real filters in a fixed orthogonal basis

For one fixed real matrix `H`, sandwich a diagonal weight matrix between `H`
and its transpose. Symmetry requires no orthogonality. When `Hᵀ * H = 1`,
composition multiplies weights pointwise, and any finite list of such linear
filters collapses to one filter. This statement keeps the basis and each
weight function fixed; it makes no claim about nonlinear or adaptive layers.
-/

noncomputable section

namespace InfoGeometry.Algebra.SpectralFilter

open InfoGeometry.Core.IdempotencyDefect

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A diagonal weight operator transported by a real matrix and its transpose. -/
def filter (H : Matrix n n ℝ) (w : n → ℝ) : Matrix n n ℝ :=
  H * Matrix.diagonal w * H.transpose

variable (H : Matrix n n ℝ)

@[simp] theorem filter_transpose (w : n → ℝ) :
    (filter H w).transpose = filter H w := by
  simp only [filter, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, mul_assoc]

theorem filter_sub (u v : n → ℝ) :
    filter H (u - v) = filter H u - filter H v := by
  change H * Matrix.diagonal (fun i => u i - v i) * H.transpose =
    H * Matrix.diagonal u * H.transpose - H * Matrix.diagonal v * H.transpose
  rw [← Matrix.diagonal_sub, mul_sub, sub_mul]

variable (hH : H.transpose * H = 1)
include hH

/-- For finite square matrices, the left inverse is also a right inverse. -/
theorem mul_transpose_eq_one : H * H.transpose = 1 :=
  mul_eq_one_comm.mp hH

@[simp] theorem filter_one : filter H 1 = 1 := by
  simpa only [filter, Matrix.diagonal_one', mul_one] using mul_transpose_eq_one H hH

theorem filter_mul (u v : n → ℝ) :
    filter H u * filter H v = filter H (u * v) := by
  calc
    filter H u * filter H v =
        H * Matrix.diagonal u * (H.transpose * H) * Matrix.diagonal v * H.transpose := by
      simp only [filter, mul_assoc]
    _ = H * (Matrix.diagonal u * Matrix.diagonal v) * H.transpose := by
      rw [hH]
      simp only [mul_one, mul_assoc]
    _ = filter H (u * v) := by
      rw [Matrix.diagonal_mul_diagonal']
      rfl

theorem filter_commute (u v : n → ℝ) : Commute (filter H u) (filter H v) := by
  change filter H u * filter H v = filter H v * filter H u
  rw [filter_mul H hH, filter_mul H hH, mul_comm u v]

theorem filter_readback (w : n → ℝ) :
    H.transpose * filter H w * H = Matrix.diagonal w := by
  calc
    H.transpose * filter H w * H =
        (H.transpose * H) * Matrix.diagonal w * (H.transpose * H) := by
      simp only [filter, mul_assoc]
    _ = Matrix.diagonal w := by rw [hH]; simp only [one_mul, mul_one]

theorem filter_injective : Function.Injective (filter H) := by
  intro u v huv
  apply Matrix.diagonal_injective
  simpa only [filter_readback H hH] using
    congrArg (fun A => H.transpose * A * H) huv

/-- The matrix defect is the filter of the pointwise scalar defect. -/
theorem defect_filter (w : n → ℝ) :
    defect (filter H w) = filter H (defect w) := by
  simp only [defect, filter_mul H hH, filter_sub]

/-- Products of frozen filters in one basis are products of their weights. -/
theorem filter_list_prod (weights : List (n → ℝ)) :
    (weights.map (filter H)).prod = filter H weights.prod := by
  induction weights with
  | nil => simp only [List.map_nil, List.prod_nil, filter_one H hH]
  | cons w weights ih =>
      simp only [List.map_cons, List.prod_cons, ih, filter_mul H hH]

/-- These filters are idempotent exactly when every spectral weight is binary. -/
theorem filter_idempotent_iff (w : n → ℝ) :
    IsIdempotentElem (filter H w) ↔ ∀ i, w i = 0 ∨ w i = 1 := by
  change filter H w * filter H w = filter H w ↔ _
  rw [filter_mul H hH, (filter_injective H hH).eq_iff]
  constructor
  · intro hw i
    have hi : w i * w i = w i := congrFun hw i
    have hz : w i * (w i - 1) = 0 := by
      rw [mul_sub, mul_one, hi, sub_self]
    rcases mul_eq_zero.mp hz with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  · intro hw
    funext i
    rcases hw i with hi | hi <;> simp [hi]

end InfoGeometry.Algebra.SpectralFilter
