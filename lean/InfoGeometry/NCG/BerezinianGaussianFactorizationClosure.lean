/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.BerezinianGaussianFactorization

/-!
# Berezinian Schur inverse independence

The Schur-complement Berezinian owner stores a matrix inverse and a scalar
inverse-determinant as explicit arguments.  This file proves that the
readout is independent of those choices whenever they satisfy the existing
(two-sided and right-inverse) laws.
-/

namespace InfoGeometry.NCG

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "SubMat" => Matrix ι ι R

/-- A two-sided inverse of a matrix is unique. -/
theorem twoSidedMatrixInverse_unique
    {D invD₁ invD₂ : SubMat}
    (h₁ : TwoSidedMatrixInverse D invD₁)
    (h₂ : TwoSidedMatrixInverse D invD₂) :
    invD₁ = invD₂ := by
  calc
    invD₁ = invD₁ * 1 := by rw [mul_one]
    _ = invD₁ * (D * invD₂) := by rw [h₂.right_inv]
    _ = (invD₁ * D) * invD₂ := by rw [mul_assoc]
    _ = 1 * invD₂ := by rw [h₁.left_inv]
    _ = invD₂ := by rw [one_mul]

/-- A right inverse of a scalar in a commutative ring is unique. -/
theorem rightInverse_unique
    {d x y : R}
    (hx : d * x = 1)
    (hy : d * y = 1) :
    x = y := by
  calc
    x = 1 * x := by rw [one_mul]
    _ = (d * y) * x := by rw [hy]
    _ = y * (d * x) := by ring
    _ = y * 1 := by rw [hx]
    _ = y := by rw [mul_one]

/-- The Schur-complement Berezinian is independent of the chosen
(two-sided) inverse of the denominator block. -/
theorem berezinianSchur_eq_of_twoSidedMatrixInverse
    (A B C D invD₁ invD₂ : SubMat) (invDetD : R)
    (h₁ : TwoSidedMatrixInverse D invD₁)
    (h₂ : TwoSidedMatrixInverse D invD₂) :
    berezinianSchur A B C D invD₁ invDetD =
      berezinianSchur A B C D invD₂ invDetD := by
  rw [twoSidedMatrixInverse_unique h₁ h₂]

/-- The Schur-complement Berezinian is independent of the chosen scalar
right-inverse of the denominator determinant. -/
theorem berezinianSchur_eq_of_rightInverseDet
    (A B C D invD : SubMat) (invDetD₁ invDetD₂ : R)
    (h₁ : Matrix.det D * invDetD₁ = 1)
    (h₂ : Matrix.det D * invDetD₂ = 1) :
    berezinianSchur A B C D invD invDetD₁ =
      berezinianSchur A B C D invD invDetD₂ := by
  rw [rightInverse_unique h₁ h₂]

end

end InfoGeometry.NCG
