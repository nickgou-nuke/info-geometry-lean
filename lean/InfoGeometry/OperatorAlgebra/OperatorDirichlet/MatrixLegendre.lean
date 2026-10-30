/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Legendre transform of a matrix quadratic form: the inverse operator is the dual Hessian

Let `A` be a real symmetric invertible matrix and `f(x) = ½ ⟨x, A x⟩`.

1. **Completing the square** (no positivity needed):
   `⟨x, y⟩ - f(x) = ½ ⟨y, A⁻¹ y⟩ - ½ ⟨x - A⁻¹y, A (x - A⁻¹y)⟩`.
2. **Fenchel–Young** for positive definite `A`:
   `⟨x, y⟩ ≤ ½⟨x, A x⟩ + ½⟨y, A⁻¹ y⟩`, with equality at `x = A⁻¹ y`.
3. **Legendre conjugate**: `½⟨y, A⁻¹y⟩` is the greatest value of
   `x ↦ ⟨x, y⟩ - ½⟨x, A x⟩`.
4. **Primal–dual Hessian product**: `A * A⁻¹ = 1`; the conjugate of the
   conjugate has Hessian `(A⁻¹)⁻¹ = A`.

`A` is an arbitrary symmetric matrix, not diagonal. The one-dimensional scalar
case is in `InfoGeometry.Fenchel`.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form `⟨x, A x⟩`. -/
def quadForm (A : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

section Symmetric

variable {A : Matrix n n ℝ} (hA : Aᵀ = A) (hdet : IsUnit A.det)
include hA hdet

omit hA in
theorem mulVec_inv_mulVec (y : n → ℝ) : A *ᵥ (A⁻¹ *ᵥ y) = y := by
  rw [mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]

/-- Completing the square for a symmetric invertible quadratic form. -/
theorem legendre_complete_square (x y : n → ℝ) :
    x ⬝ᵥ y - (1 / 2) * quadForm A x =
      (1 / 2) * quadForm A⁻¹ y - (1 / 2) * quadForm A (x - A⁻¹ *ᵥ y) := by
  set w := A⁻¹ *ᵥ y with hw
  have hAw : A *ᵥ w = y := mulVec_inv_mulVec hdet y
  have hsym : w ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, hAw]
  have hyw : quadForm A⁻¹ y = y ⬝ᵥ w := rfl
  rw [hyw]
  simp only [quadForm, mulVec_sub, sub_dotProduct, dotProduct_sub, hAw, hsym]
  rw [dotProduct_comm w y, dotProduct_comm x y]
  ring

end Symmetric

section PositiveDefinite

variable {A : Matrix n n ℝ} (hA : A.PosDef)
include hA

omit [Fintype n] [DecidableEq n] in
theorem posDef_transpose_eq : Aᵀ = A := by
  have h := hA.1
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem posDef_det_isUnit : IsUnit A.det :=
  (isUnit_iff_isUnit_det A).mp hA.isUnit

omit [DecidableEq n] in
theorem quadForm_nonneg (v : n → ℝ) : 0 ≤ quadForm A v := by
  have h := hA.posSemidef.dotProduct_mulVec_nonneg v
  simpa [quadForm] using h

/-- Fenchel–Young inequality for a matrix quadratic form. -/
theorem fenchel_young (x y : n → ℝ) :
    x ⬝ᵥ y ≤ (1 / 2) * quadForm A x + (1 / 2) * quadForm A⁻¹ y := by
  have h := legendre_complete_square (posDef_transpose_eq hA) (posDef_det_isUnit hA) x y
  have h0 := quadForm_nonneg hA (x - A⁻¹ *ᵥ y)
  linarith

/-- Equality in Fenchel–Young holds at the dual point `x = A⁻¹ y`. -/
theorem fenchel_young_eq (y : n → ℝ) :
    (A⁻¹ *ᵥ y) ⬝ᵥ y - (1 / 2) * quadForm A (A⁻¹ *ᵥ y) = (1 / 2) * quadForm A⁻¹ y := by
  rw [legendre_complete_square (posDef_transpose_eq hA) (posDef_det_isUnit hA), sub_self]
  simp [quadForm]

/-- The Legendre conjugate of `½⟨x, A x⟩` is `½⟨y, A⁻¹ y⟩`. -/
theorem legendre_conjugate_isGreatest (y : n → ℝ) :
    IsGreatest (Set.range fun x : n → ℝ => x ⬝ᵥ y - (1 / 2) * quadForm A x)
      ((1 / 2) * quadForm A⁻¹ y) := by
  refine ⟨⟨A⁻¹ *ᵥ y, fenchel_young_eq hA y⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  have := fenchel_young hA x y
  linarith

/-- Primal and dual Hessians are mutually inverse, and dualizing twice returns `A`. -/
theorem hessian_product :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 ∧ A⁻¹⁻¹ = A :=
  ⟨mul_nonsing_inv A (posDef_det_isUnit hA), nonsing_inv_mul A (posDef_det_isUnit hA),
    nonsing_inv_nonsing_inv A (posDef_det_isUnit hA)⟩

end PositiveDefinite

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
