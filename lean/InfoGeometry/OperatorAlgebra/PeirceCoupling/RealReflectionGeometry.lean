/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.StarReflection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Full real matrix geometry of the reflected Gram operator

All matrices have real coefficients. No diagonalization or simultaneous
commutativity is assumed. Positive definiteness requires a trivial common
kernel; nonzero coupling alone is not used as a substitute.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling.RealReflectionGeometry

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading

variable {n : Type*} [Fintype n]

theorem gram_posSemidef (N : Matrix n n ℝ) :
    (N * Nᴴ + Nᴴ * N).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose N).add
    (Matrix.posSemidef_conjTranspose_mul_self N)

theorem gram_mulVec_eq_zero_iff (N : Matrix n n ℝ) (v : n → ℝ) :
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

theorem gram_ker (N : Matrix n n ℝ) :
    LinearMap.ker (N * Nᴴ + Nᴴ * N).mulVecLin =
      LinearMap.ker N.mulVecLin ⊓ LinearMap.ker Nᴴ.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_inf,
    gram_mulVec_eq_zero_iff]

theorem gram_posDef_iff (N : Matrix n n ℝ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      ∀ v : n → ℝ, N *ᵥ v = 0 ∧ Nᴴ *ᵥ v = 0 → v = 0 := by
  constructor
  · intro h v hv
    by_contra hv0
    have hz := (gram_mulVec_eq_zero_iff N v).mpr hv
    have hpos := h.dotProduct_mulVec_pos hv0
    rw [hz, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro h
    have hPSD := gram_posSemidef N
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hPSD.isHermitian ?_
    intro v hv
    refine lt_of_le_of_ne (hPSD.dotProduct_mulVec_nonneg v) ?_
    intro hzero
    exact hv (h v ((gram_mulVec_eq_zero_iff N v).mp
      (hPSD.dotProduct_mulVec_zero_iff.mp hzero.symm)))

variable [DecidableEq n]

theorem reflected_gram_posSemidef {p : Matrix n n ℝ}
    (hp : IsStarProjection p) (a : Matrix n n ℝ) :
    (-((reflection p * star (component10 p a) * reflection p) * component10 p a +
      component10 p a * (reflection p * star (component10 p a) * reflection p))).PosSemidef := by
  rw [starReflection_gram_identity hp a]
  exact gram_posSemidef (component10 p a)

theorem reflected_star_pairing_trace_zero {p : Matrix n n ℝ}
    (hp : IsStarProjection p) (a : Matrix n n ℝ) :
    Matrix.trace (star (reflection p * star (component10 p a) * reflection p) *
      component10 p a) = 0 := by
  rw [starReflection_star_pairing_zero hp a, Matrix.trace_zero]

end InfoGeometry.OperatorAlgebra.PeirceCoupling.RealReflectionGeometry
