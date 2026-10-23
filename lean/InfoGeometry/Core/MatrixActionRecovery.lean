/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Mul

/-! # Row and column zero tests from one-sided matrix recovery -/
namespace InfoGeometry.Core.MatrixActionRecovery
open Matrix
variable {n : Type*} [Fintype n]

variable {R : Type*} [Semiring R] {S A B : Matrix n n R}

/-- Matrix right annihilation descends to every row in the image of S. -/
theorem row_annihilation (h : S * A = 0) (v : n → R) :
    (v ᵥ* S) ᵥ* A = 0 := by
  rw [vecMul_vecMul, h, vecMul_zero]

/-- A right recovery factor makes the row zero test faithful on the image of S. -/
theorem row_zero_iff_of_recovery (h : (S * A) * B = S) (v : n → R) :
    (v ᵥ* S) ᵥ* A = 0 ↔ v ᵥ* S = 0 := by
  constructor
  · intro hz
    calc
      v ᵥ* S = ((v ᵥ* S) ᵥ* A) ᵥ* B := by
        simp only [vecMul_vecMul, h]
      _ = 0 := by rw [hz, zero_vecMul]
  · intro hz
    rw [hz, zero_vecMul]

/-- Matrix left annihilation descends to every column in the image of S. -/
theorem column_annihilation (h : A * S = 0) (v : n → R) :
    A *ᵥ (S *ᵥ v) = 0 := by
  rw [mulVec_mulVec, h, zero_mulVec]

/-- A left recovery factor makes the column zero test faithful on the image of S. -/
theorem column_zero_iff_of_recovery (h : B * (A * S) = S) (v : n → R) :
    A *ᵥ (S *ᵥ v) = 0 ↔ S *ᵥ v = 0 := by
  constructor
  · intro hz
    calc
      S *ᵥ v = B *ᵥ (A *ᵥ (S *ᵥ v)) := by
        simp only [mulVec_mulVec, h]
      _ = 0 := by rw [hz, mulVec_zero]
  · intro hz
    rw [hz, mulVec_zero]


end InfoGeometry.Core.MatrixActionRecovery
