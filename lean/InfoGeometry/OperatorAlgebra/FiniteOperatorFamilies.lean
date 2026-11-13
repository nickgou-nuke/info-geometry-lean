/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Star.StarProjection

/-!
# Finite weighted families over a star ring

The family entries and weights are elements of an arbitrary, possibly
noncommutative star ring. Their ordered sandwich sum and the native outer
product matrix satisfy algebraic adjoint, complement, and projection laws.
There is no Hilbert-space vector, norm, Gabor lattice, or porosity assertion.

The matrix construction is Mathlib's `Matrix.vecMulVec`. In particular, its
diagonal sum is already given by `Matrix.trace_vecMulVec` in
`Mathlib.LinearAlgebra.Matrix.Trace`; no cyclic-trace law over noncommutative
coefficients is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteOperatorFamilies

open scoped BigOperators

variable {A ι : Type*} [Ring A] [StarRing A] [Fintype ι]

/-- Ordered finite sandwich sum with operator-valued weights. -/
def multiplier (φ b : ι → A) : A := ∑ i, φ i * b i * star (φ i)

/-- Taking adjoints conjugates each weight and preserves its sandwich order. -/
theorem star_multiplier (φ b : ι → A) :
    star (multiplier φ b) = multiplier φ (star b) := by
  simp only [multiplier, star_sum, star_mul, star_star, Pi.star_apply, mul_assoc]

/-- Complementary operator-valued weights sum to the native family dot product. -/
theorem multiplier_complement_add (φ b : ι → A) :
    multiplier φ (fun i => 1 - b i) + multiplier φ b = dotProduct φ (star φ) := by
  unfold multiplier dotProduct
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_sub, mul_one, sub_mul, sub_add_cancel, Pi.star_apply]

omit [Fintype ι] in
/-- The native outer product is self-adjoint without commuting coefficients. -/
theorem vecMulVec_star_isSelfAdjoint (φ : ι → A) :
    IsSelfAdjoint (Matrix.vecMulVec (star φ) φ) := by
  change star (Matrix.vecMulVec (star φ) φ) = Matrix.vecMulVec (star φ) φ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec]
  ext i j
  change star (φ i) * star (star (φ j)) = star (φ i) * φ j
  rw [star_star]

/-- The ordered normalization makes the native outer product an actual star
projection. Reversing the normalization factors is not assumed valid. -/
theorem vecMulVec_star_isStarProjection (φ : ι → A)
    (hφ : dotProduct φ (star φ) = 1) :
    IsStarProjection (Matrix.vecMulVec (star φ) φ) := by
  refine ⟨?_, vecMulVec_star_isSelfAdjoint φ⟩
  change Matrix.vecMulVec (star φ) φ * Matrix.vecMulVec (star φ) φ =
    Matrix.vecMulVec (star φ) φ
  rw [Matrix.vecMulVec_mul_vecMulVec, hφ, one_smul]

end InfoGeometry.OperatorAlgebra.FiniteOperatorFamilies
