/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coisometric coarse-graining and its retained subspace

For a rectangular matrix `Q` satisfying `Q * Qᴴ = 1`, the retained fine-space
operator is the native star projection `Qᴴ * Q`. Its complementary range is
exactly the kernel of coarse-graining. These statements allow arbitrary finite
dimensions and do not require the fine-space operators to commute with that
projection.

In Dimock, *The Renormalization Group According to Balaban, I. Small Fields*,
section 2.1, the coisometry law uses the lattice's weighted inner products.
The law here is an explicit hypothesis in orthonormal coordinates; it is not
asserted for an unnormalized arithmetic-mean matrix.
-/

namespace InfoGeometry.OperatorAlgebra.CoisometricCoarseGraining

open Matrix

variable {n m l 𝕜 : Type*} [Fintype n] [Fintype m] [Fintype l]
  [DecidableEq n] [DecidableEq m] [DecidableEq l] [RCLike 𝕜]

omit [DecidableEq n] in
/-- The retained fine-space operator is a self-adjoint idempotent. -/
theorem projection_isStarProjection (Q : Matrix m n 𝕜)
    (hQ : Q * Qᴴ = 1) : IsStarProjection (Qᴴ * Q) where
  isIdempotentElem := by
    change (Qᴴ * Q) * (Qᴴ * Q) = Qᴴ * Q
    calc
      _ = Qᴴ * (Q * Qᴴ) * Q := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ, Matrix.mul_one]
  isSelfAdjoint := (Matrix.isHermitian_conjTranspose_mul_self Q).isSelfAdjoint

/-- Coarse-graining kills the complementary fine-space component. -/
theorem mul_complement_eq_zero (Q : Matrix m n 𝕜)
    (hQ : Q * Qᴴ = 1) : Q * (1 - Qᴴ * Q) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQ,
    Matrix.one_mul, sub_self]

/-- The adjoint inclusion has no component in the complementary subspace. -/
theorem complement_mul_adjoint_eq_zero (Q : Matrix m n 𝕜)
    (hQ : Q * Qᴴ = 1) : (1 - Qᴴ * Q) * Qᴴ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ,
    Matrix.mul_one, sub_self]

omit [Fintype l] [DecidableEq n] in
/-- Rectangular coisometries compose without choosing a common square carrier. -/
theorem mul_coisometry (Q₁ : Matrix m n 𝕜) (Q₂ : Matrix l m 𝕜)
    (hQ₁ : Q₁ * Q₁ᴴ = 1) (hQ₂ : Q₂ * Q₂ᴴ = 1) :
    (Q₂ * Q₁) * (Q₂ * Q₁)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Q₂ * (Q₁ * Q₁ᴴ) * Q₂ᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQ₁, Matrix.mul_one, hQ₂]

omit [DecidableEq n] in
/-- The retained projection and coarse-graining have exactly the same kernel. -/
theorem ker_projection_eq (Q : Matrix m n 𝕜) (hQ : Q * Qᴴ = 1) :
    LinearMap.ker (Qᴴ * Q).mulVecLin = LinearMap.ker Q.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    have hxQ := congrArg (fun v => Q *ᵥ v) hx
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQ,
      Matrix.one_mul, Matrix.mulVec_zero] using hxQ
  · intro hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

omit [DecidableEq n] in
/-- The retained subspace is precisely the range of the adjoint inclusion. -/
theorem range_projection_eq (Q : Matrix m n 𝕜) (hQ : Q * Qᴴ = 1) :
    LinearMap.range (Qᴴ * Q).mulVecLin = LinearMap.range Qᴴ.mulVecLin := by
  ext x
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Q *ᵥ y, Matrix.mulVec_mulVec y Qᴴ Q⟩
  · rintro ⟨y, rfl⟩
    refine ⟨Qᴴ *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]

/-- The discarded subspace is the actual kernel of coarse-graining. -/
theorem range_complement_eq_ker (Q : Matrix m n 𝕜) (hQ : Q * Qᴴ = 1) :
    LinearMap.range (1 - Qᴴ * Q).mulVecLin = LinearMap.ker Q.mulVecLin := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_mulVec, mul_complement_eq_zero Q hQ, Matrix.zero_mulVec]
  · intro hx
    refine ⟨x, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hx, Matrix.mulVec_zero, sub_zero]

end InfoGeometry.OperatorAlgebra.CoisometricCoarseGraining
