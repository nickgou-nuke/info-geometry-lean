/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith

/-!
# Three-square faithfulness for bounded real Hilbert operators

This discharges the algebraic three-star-square hypothesis on the full
noncommutative algebra of bounded real Hilbert operators. The star is the
positive Hilbert adjoint, not an indefinite Krein adjoint. No finite-dimensional
or diagonal hypothesis is imposed.
-/

namespace InfoGeometry.Analysis.RealStarSquareFaithfulness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A vanishing sum of three Hilbert-adjoint squares forces the first
operator to vanish. This is the exact hypothesis used by shifted localization. -/
theorem three_star_squares_first (X Y Z : E →L[ℝ] E)
    (h : star X * X + star Y * Y + star Z * Z = 0) : X = 0 := by
  ext x
  have he := congrArg (fun T : E →L[ℝ] E => inner ℝ (T x) x) h
  simp only [add_apply, mul_apply_eq_comp, inner_add_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    zero_apply, inner_zero_left] at he
  have hX : 0 ≤ inner ℝ (X x) (X x) := real_inner_self_nonneg
  have hY : 0 ≤ inner ℝ (Y x) (Y x) := real_inner_self_nonneg
  have hZ : 0 ≤ inner ℝ (Z x) (Z x) := real_inner_self_nonneg
  have hx : inner ℝ (X x) (X x) = 0 := by linarith
  exact inner_self_eq_zero.mp hx

/-- All three operators vanish, with their original multiplication order. -/
theorem three_star_squares_eq_zero (X Y Z : E →L[ℝ] E)
    (h : star X * X + star Y * Y + star Z * Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  have hX := three_star_squares_first X Y Z h
  have hY := three_star_squares_first Y X Z (by
    simpa only [add_comm, add_left_comm, add_assoc] using h)
  have hZ := three_star_squares_first Z X Y (by
    simpa only [add_comm, add_left_comm, add_assoc] using h)
  exact ⟨hX, hY, hZ⟩

/-- In particular the full bounded-operator star is proper. -/
theorem star_square_eq_zero (X : E →L[ℝ] E) (h : star X * X = 0) : X = 0 :=
  three_star_squares_first X 0 0 (by simpa using h)

end InfoGeometry.Analysis.RealStarSquareFaithfulness
