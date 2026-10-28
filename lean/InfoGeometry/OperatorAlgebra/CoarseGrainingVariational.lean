/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
import Mathlib.Tactic.Abel

/-!
# Exact quadratic minimization for positive operator coarse-graining

The quadratic energy is the real part of the actual Hermitian matrix form.
Mathlib's rectangular Schur-complement identity gives square completion;
strict positivity gives the unique minimizer. No diagonalization or
commutation hypothesis is used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PositiveCoarseGraining

open Matrix
open scoped ComplexOrder

variable {𝕜 n m : Type*} [RCLike 𝕜]
variable [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Fine energy plus the matrix-weighted discrepancy from a coarse state. -/
def quadraticEnergy (A : Matrix n n 𝕜) (R : Matrix m m 𝕜) (Q : Matrix m n 𝕜)
    (y : m → 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ (A *ᵥ x)) +
    RCLike.re (star (y - Q *ᵥ x) ⬝ᵥ (R *ᵥ (y - Q *ᵥ x)))

variable {A : Matrix n n 𝕜} {R : Matrix m m 𝕜} (Q : Matrix m n 𝕜)

omit [DecidableEq n] [DecidableEq m] in
/-- Identify the block quadratic form with the original weighted discrepancy. -/
theorem block_quadratic_eq (hR : R.IsHermitian) (y : m → 𝕜) (x : n → 𝕜) :
    (star (y ⊕ᵥ x)) ᵥ*
        Matrix.fromBlocks R (-(R * Q)) (-(R * Q))ᴴ (finePrecision A R Q) ⬝ᵥ
          (y ⊕ᵥ x) =
      star x ⬝ᵥ (A *ᵥ x) +
        star (y - Q *ᵥ x) ⬝ᵥ (R *ᵥ (y - Q *ᵥ x)) := by
  simp [Function.star_sumElim, Matrix.vecMul_fromBlocks, finePrecision,
    Matrix.conjTranspose_mul, hR.eq, Matrix.mulVec_sub,
    Matrix.sub_vecMul, star_sub, Matrix.star_mulVec, dotProduct_sub,
    sub_dotProduct, Matrix.vecMul_add, Matrix.vecMul_neg,
    Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  abel

omit [DecidableEq m] in
/-- Exact square completion before taking real parts. -/
theorem quadratic_completion (hA : A.PosDef) (hR : R.PosDef)
    (y : m → 𝕜) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x) +
        star (y - Q *ᵥ x) ⬝ᵥ (R *ᵥ (y - Q *ᵥ x)) =
      star y ⬝ᵥ (coarsePrecision A R Q *ᵥ y) +
        star (x - harmonicExtension A R Q *ᵥ y) ⬝ᵥ
          (finePrecision A R Q *ᵥ (x - harmonicExtension A R Q *ᵥ y)) := by
  have hH := finePrecision_posDef Q hA hR
  let := hH.isUnit.invertible
  have h := Matrix.schur_complement_eq₂₂ R (-(R * Q)) y x hH.isHermitian
  rw [block_quadratic_eq Q hR.isHermitian] at h
  have hshift :
      ((finePrecision A R Q)⁻¹ * (-(R * Q))ᴴ) *ᵥ y + x =
        x - harmonicExtension A R Q *ᵥ y := by
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hR.isHermitian.eq,
      Matrix.mul_neg, Matrix.neg_mulVec, harmonicExtension, ← Matrix.mul_assoc]
    abel
  have hschur :
      R - (-(R * Q)) * (finePrecision A R Q)⁻¹ * (-(R * Q))ᴴ =
        coarsePrecision A R Q := by
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hR.isHermitian.eq,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, coarsePrecision, Matrix.mul_assoc]
  rw [hshift, hschur] at h
  simpa only [Matrix.dotProduct_mulVec, add_comm] using h

omit [DecidableEq m] in
/-- Energy splits into its coarse minimum and a strictly positive fine residual. -/
theorem quadraticEnergy_completion (hA : A.PosDef) (hR : R.PosDef)
    (y : m → 𝕜) (x : n → 𝕜) :
    quadraticEnergy A R Q y x =
      RCLike.re (star y ⬝ᵥ (coarsePrecision A R Q *ᵥ y)) +
        RCLike.re (star (x - harmonicExtension A R Q *ᵥ y) ⬝ᵥ
          (finePrecision A R Q *ᵥ (x - harmonicExtension A R Q *ᵥ y))) := by
  simpa only [quadraticEnergy, map_add] using
    congrArg RCLike.re (quadratic_completion Q hA hR y x)

omit [DecidableEq n] [DecidableEq m] in
/-- Positive definiteness characterizes the vanishing real quadratic form. -/
theorem quadratic_re_eq_zero_iff (hA : A.PosDef) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (ne_of_gt (hA.re_dotProduct_pos hx)) h
  · rintro rfl
    simp

omit [DecidableEq m] in
theorem quadraticEnergy_lower_bound (hA : A.PosDef) (hR : R.PosDef)
    (y : m → 𝕜) (x : n → 𝕜) :
    RCLike.re (star y ⬝ᵥ (coarsePrecision A R Q *ᵥ y)) ≤ quadraticEnergy A R Q y x := by
  rw [quadraticEnergy_completion Q hA hR]
  exact le_add_of_nonneg_right
    ((finePrecision_posDef Q hA hR).posSemidef.re_dotProduct_nonneg _)

omit [DecidableEq m] in
/-- Equality in the lower bound identifies exactly the harmonic extension. -/
theorem quadraticEnergy_eq_min_iff (hA : A.PosDef) (hR : R.PosDef)
    (y : m → 𝕜) (x : n → 𝕜) :
    quadraticEnergy A R Q y x =
        RCLike.re (star y ⬝ᵥ (coarsePrecision A R Q *ᵥ y)) ↔
      x = harmonicExtension A R Q *ᵥ y := by
  rw [quadraticEnergy_completion Q hA hR, add_eq_left,
    quadratic_re_eq_zero_iff (finePrecision_posDef Q hA hR), sub_eq_zero]

omit [DecidableEq m] in
theorem quadraticEnergy_at_harmonicExtension (hA : A.PosDef) (hR : R.PosDef)
    (y : m → 𝕜) :
    quadraticEnergy A R Q y (harmonicExtension A R Q *ᵥ y) =
      RCLike.re (star y ⬝ᵥ (coarsePrecision A R Q *ᵥ y)) :=
  (quadraticEnergy_eq_min_iff Q hA hR y _).2 rfl

omit [DecidableEq m] in
/-- A global minimizer exists and is characterized without an existence assumption. -/
theorem is_minimizer_iff (hA : A.PosDef) (hR : R.PosDef)
    (y : m → 𝕜) (x : n → 𝕜) :
    (∀ z, quadraticEnergy A R Q y x ≤ quadraticEnergy A R Q y z) ↔
      x = harmonicExtension A R Q *ᵥ y := by
  constructor
  · intro h
    apply (quadraticEnergy_eq_min_iff Q hA hR y x).1
    refine le_antisymm ?_ (quadraticEnergy_lower_bound Q hA hR y x)
    simpa only [quadraticEnergy_at_harmonicExtension Q hA hR] using
      h (harmonicExtension A R Q *ᵥ y)
  · rintro rfl z
    rw [quadraticEnergy_at_harmonicExtension Q hA hR]
    exact quadraticEnergy_lower_bound Q hA hR y z

end InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
