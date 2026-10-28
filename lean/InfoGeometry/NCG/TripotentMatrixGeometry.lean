/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.Drazin
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Star.StarProjection

/-! # Support, generalized inverse, and kernel of a tripotent matrix

Tripotency is algebraic. Orthogonality and unitarity are asserted only with
the explicit self-adjointness hypotheses in the star section.
-/
namespace InfoGeometry.NCG.TripotentMatrixGeometry

open Matrix InfoGeometry.Singular.MoorePenrose InfoGeometry.Singular.Drazin

variable {n : Type*} [Fintype n] [DecidableEq n]

section Ring
variable {R : Type*} [Ring R] {T : Matrix n n R} (hT : T * T * T = T)

include hT

theorem self_drazin : IsDrazinInverse T T 1 := by
  refine IsDrazinInverse.mk hT rfl ?_
  simpa only [pow_one, pow_two] using hT.symm

theorem square_idempotent : IsIdempotentElem (T * T) := by
  change (T * T) * (T * T) = T * T
  calc
    _ = (T * T * T) * T := by simp only [mul_assoc]
    _ = T * T := by rw [hT]

theorem complement_idempotent : IsIdempotentElem (1 - T * T) :=
  (square_idempotent hT).one_sub

theorem complement_mul : (1 - T * T) * T = 0 := by
  rw [sub_mul, one_mul, hT, sub_self]

theorem mul_complement : T * (1 - T * T) = 0 := by
  rw [mul_sub, mul_one, ← mul_assoc, hT, sub_self]

theorem completion_sq : (1 - T * T + T) * (1 - T * T + T) = 1 := by
  have hc := (complement_idempotent hT).eq
  have hl := complement_mul hT
  have hr := mul_complement hT
  calc
    _ = (1 - T * T) * (1 - T * T) + (1 - T * T) * T +
        T * (1 - T * T) + T * T := by noncomm_ring
    _ = 1 := by rw [hc, hl, hr]; noncomm_ring

theorem completion_isUnit : IsUnit (1 - T * T + T) :=
  ⟨⟨1 - T * T + T, 1 - T * T + T, completion_sq hT, completion_sq hT⟩, rfl⟩

section Star
variable [StarRing R]

omit hT in
/-- Tripotency and a Hermitian square are the exact self-Penrose conditions. -/
theorem self_moorePenrose_iff :
    IsMoorePenroseInverse T T ↔ T * T * T = T ∧ IsSelfAdjoint (T * T) := by
  constructor
  · intro h
    exact ⟨h.aba_eq_a, h.ab_adj_eq⟩
  · rintro ⟨hc, hs⟩
    exact ⟨hc, hc, hs, hs⟩

theorem self_moorePenrose_of_isSelfAdjoint (hs : IsSelfAdjoint T) :
    IsMoorePenroseInverse T T := by
  apply self_moorePenrose_iff.mpr
  exact ⟨hT, by change star (T * T) = T * T; rw [star_mul, hs.star_eq]⟩

theorem completion_mem_unitary (hs : IsSelfAdjoint T) :
    1 - T * T + T ∈ unitary (Matrix n n R) := by
  have hstar : star (1 - T * T + T) = 1 - T * T + T := by
    simp only [star_add, star_sub, star_one, star_mul, hs.star_eq]
  constructor <;> rw [hstar, completion_sq hT]

end Star
end Ring

section Kernel
variable {K : Type*} [CommRing K] {T : Matrix n n K} (hT : T * T * T = T)

include hT

/-- The algebraic complement fixes exactly the kernel vectors. -/
theorem complement_mulVec_eq_self_iff (v : n → K) :
    (1 - T * T) *ᵥ v = v ↔ T *ᵥ v = 0 := by
  constructor
  · intro h
    calc
      T *ᵥ v = T *ᵥ ((1 - T * T) *ᵥ v) := by rw [h]
      _ = (T * (1 - T * T)) *ᵥ v := (mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [mul_complement hT, zero_mulVec]
  · intro h
    rw [sub_mulVec, one_mulVec, mulVec_mulVec, h, mulVec_zero, sub_zero]

/-- A native submodule equality, without a basis change or division. -/
theorem range_complement_eq_ker :
    LinearMap.range (1 - T * T).mulVecLin = LinearMap.ker T.mulVecLin := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change T *ᵥ ((1 - T * T) *ᵥ w) = 0
    rw [← mulVec_mulVec, mul_complement hT, zero_mulVec]
  · intro h
    refine ⟨v, ?_⟩
    exact (complement_mulVec_eq_self_iff hT v).mpr h

end Kernel
end InfoGeometry.NCG.TripotentMatrixGeometry
