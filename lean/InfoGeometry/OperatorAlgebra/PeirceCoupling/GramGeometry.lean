/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The common kernel of two adjoint Gram operators

For an arbitrary full complex matrix `N`, the sum `N * Nᴴ + Nᴴ * N`
is positive semidefinite. Its kernel is the intersection of the kernels of
`N` and `Nᴴ`; positive definiteness is equivalent to this intersection being
zero. No nilpotency hypothesis is used in this file.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n]

/-- The sum of the two adjoint Gram operators is positive semidefinite. -/
theorem gramSum_posSemidef (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose N).add
    (Matrix.posSemidef_conjTranspose_mul_self N)

/-- A vector is annihilated by the Gram sum exactly when both arrows annihilate it. -/
theorem gramSum_mulVec_eq_zero_iff (N : Matrix n n ℂ) (v : n → ℂ) :
    (N * Nᴴ + Nᴴ * N) *ᵥ v = 0 ↔ N *ᵥ v = 0 ∧ Nᴴ *ᵥ v = 0 := by
  have hP := Matrix.posSemidef_self_mul_conjTranspose N
  have hQ := Matrix.posSemidef_conjTranspose_mul_self N
  constructor
  · intro hv
    have hsum : star v ⬝ᵥ ((N * Nᴴ) *ᵥ v) +
        star v ⬝ᵥ ((Nᴴ * N) *ᵥ v) = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hv, dotProduct_zero]
    have hparts := (add_eq_zero_iff_of_nonneg
      (hP.dotProduct_mulVec_nonneg v) (hQ.dotProduct_mulVec_nonneg v)).mp hsum
    exact ⟨(Matrix.conjTranspose_mul_self_mulVec_eq_zero N v).mp
        (hQ.dotProduct_mulVec_zero_iff.mp hparts.2),
      (Matrix.self_mul_conjTranspose_mulVec_eq_zero N v).mp
        (hP.dotProduct_mulVec_zero_iff.mp hparts.1)⟩
  · rintro ⟨hv, hv'⟩
    rw [Matrix.add_mulVec,
      (Matrix.self_mul_conjTranspose_mulVec_eq_zero N v).mpr hv',
      (Matrix.conjTranspose_mul_self_mulVec_eq_zero N v).mpr hv, add_zero]

/-- The native linear-map kernel of the Gram sum is the common kernel. -/
theorem gramSum_ker (N : Matrix n n ℂ) :
    LinearMap.ker (N * Nᴴ + Nᴴ * N).mulVecLin =
      LinearMap.ker N.mulVecLin ⊓ LinearMap.ker Nᴴ.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_inf,
    gramSum_mulVec_eq_zero_iff]

/-- Positive definiteness is exactly the pointwise trivial-common-kernel condition. -/
theorem gramSum_posDef_iff (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      ∀ v : n → ℂ, N *ᵥ v = 0 ∧ Nᴴ *ᵥ v = 0 → v = 0 := by
  constructor
  · intro h v hv
    by_contra hv0
    have hz := (gramSum_mulVec_eq_zero_iff N v).mpr hv
    have hpos := h.dotProduct_mulVec_pos hv0
    rw [hz, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro h
    have hPSD := gramSum_posSemidef N
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hPSD.isHermitian ?_
    intro v hv
    refine lt_of_le_of_ne (hPSD.dotProduct_mulVec_nonneg v) ?_
    intro hzero
    exact hv (h v ((gramSum_mulVec_eq_zero_iff N v).mp
      (hPSD.dotProduct_mulVec_zero_iff.mp hzero.symm)))

/-- Positive definiteness in the native lattice of submodules. -/
theorem gramSum_posDef_iff_ker_inf_eq_bot (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      LinearMap.ker N.mulVecLin ⊓ LinearMap.ker Nᴴ.mulVecLin = ⊥ := by
  simpa only [Submodule.eq_bot_iff, Submodule.mem_inf, LinearMap.mem_ker,
    Matrix.mulVecLin_apply] using gramSum_posDef_iff N

/-- The Gram sum is positive definite exactly when its own kernel is zero. -/
theorem gramSum_posDef_iff_ker_eq_bot (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      LinearMap.ker (N * Nᴴ + Nᴴ * N).mulVecLin = ⊥ := by
  rw [gramSum_ker]
  exact gramSum_posDef_iff_ker_inf_eq_bot N

/-- The corresponding native matrix action is injective exactly in the positive-definite case. -/
theorem gramSum_posDef_iff_injective (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      Function.Injective (N * Nᴴ + Nᴴ * N).mulVec := by
  change (N * Nᴴ + Nᴴ * N).PosDef ↔
    Function.Injective (N * Nᴴ + Nᴴ * N).mulVecLin
  exact (gramSum_posDef_iff_ker_eq_bot N).trans LinearMap.ker_eq_bot

/-- In finite dimension the Gram sum is positive definite exactly when it is a unit. -/
theorem gramSum_posDef_iff_isUnit [DecidableEq n] (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔ IsUnit (N * Nᴴ + Nᴴ * N) :=
  (gramSum_posDef_iff_injective N).trans Matrix.mulVec_injective_iff_isUnit

/-- Cyclicity of trace identifies the two Gram traces. -/
theorem trace_gramSum (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).trace = 2 * (Nᴴ * N).trace := by
  rw [Matrix.trace_add, Matrix.trace_mul_comm N Nᴴ, two_mul]

/-- Vanishing trace detects the zero matrix, without a nilpotency hypothesis. -/
theorem trace_gramSum_eq_zero_iff (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).trace = 0 ↔ N = 0 := by
  simp only [trace_gramSum, mul_eq_zero, two_ne_zero, false_or,
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff]

/-- Strictly positive trace detects a nonzero arrow, not positive definiteness. -/
theorem trace_gramSum_pos_iff (N : Matrix n n ℂ) :
    0 < (N * Nᴴ + Nᴴ * N).trace ↔ N ≠ 0 := by
  constructor
  · intro h hN
    exact (ne_of_gt h) ((trace_gramSum_eq_zero_iff N).mpr hN)
  · intro hN
    refine lt_of_le_of_ne (gramSum_posSemidef N).trace_nonneg ?_
    intro hz
    exact hN ((trace_gramSum_eq_zero_iff N).mp hz.symm)

/-- The sum of the adjoint Gram operators vanishes exactly for the zero arrow. -/
theorem gramSum_eq_zero_iff (N : Matrix n n ℂ) :
    N * Nᴴ + Nᴴ * N = 0 ↔ N = 0 := by
  constructor
  · intro h
    apply (trace_gramSum_eq_zero_iff N).mp
    rw [h, Matrix.trace_zero]
  · intro h
    simp only [h, Matrix.conjTranspose_zero, zero_mul, add_zero]

end InfoGeometry.OperatorAlgebra.PeirceCoupling
