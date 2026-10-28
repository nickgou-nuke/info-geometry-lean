/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixPeirce
import Mathlib.LinearAlgebra.Projection

/-!
# Native submodule geometry of the matrix idempotent locus

The tangent space is the kernel of the linearized idempotent equation.
Its complementary even space and all four Peirce components are recovered uniquely.
All matrix entries and products remain arbitrary and noncommutative.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixPeirceZorn.MatrixGeometry

open InfoGeometry.Canonical.MatrixPeirceZorn.MatrixPeirce
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear term of `(p + x)² - (p + x)` at the idempotent `p`. -/
def tangentOperator (p : Mat n) : Mat n →ₗ[ℂ] Mat n :=
  cornerLinear p 1 + cornerLinear 1 p - LinearMap.id

@[simp] theorem tangentOperator_apply (p x : Mat n) :
    tangentOperator p x = p * x + x * p - x := by
  simp [tangentOperator, corner]

/-- The algebraic tangent space is a native complex submodule. -/
def tangentSpace (p : Mat n) : Submodule ℂ (Mat n) := LinearMap.ker (tangentOperator p)

@[simp] theorem mem_tangentSpace (p x : Mat n) :
    x ∈ tangentSpace p ↔ p * x + x * p = x := by
  simp [tangentSpace, sub_eq_zero]

def evenProjection (p : Mat n) : Mat n →ₗ[ℂ] Mat n :=
  cornerLinear p p + cornerLinear (complement p) (complement p)

def oddProjection (p : Mat n) : Mat n →ₗ[ℂ] Mat n :=
  cornerLinear p (complement p) + cornerLinear (complement p) p

@[simp] theorem evenProjection_apply (p x : Mat n) :
    evenProjection p x = positive p x + negative p x := rfl

@[simp] theorem oddProjection_apply (p x : Mat n) :
    oddProjection p x = raise p x + lower p x := rfl

theorem even_add_odd (p x : Mat n) : evenProjection p x + oddProjection p x = x := by
  simp only [evenProjection_apply, oddProjection_apply]
  have h := four_corner_decomposition p x
  simpa only [add_assoc, add_left_comm, add_comm] using h

theorem even_add_odd_linear (p : Mat n) :
    evenProjection p + oddProjection p = LinearMap.id := by
  ext x i j
  exact congrFun (congrFun (even_add_odd p x) i) j

@[simp] theorem even_even (p x : Mat n) (hp : p * p = p) :
    evenProjection p (evenProjection p x) = evenProjection p x := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  simp only [evenProjection_apply, positive, negative, corner, complement]
  noncomm_ring [hp, hp_left]

@[simp] theorem odd_odd (p x : Mat n) (hp : p * p = p) :
    oddProjection p (oddProjection p x) = oddProjection p x := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  simp only [oddProjection_apply, raise, lower, corner, complement]
  noncomm_ring [hp, hp_left]

@[simp] theorem even_odd (p x : Mat n) (hp : p * p = p) :
    evenProjection p (oddProjection p x) = 0 := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  simp only [evenProjection_apply, oddProjection_apply, positive, negative, raise, lower,
    corner, complement]
  noncomm_ring [hp, hp_left]

@[simp] theorem odd_even (p x : Mat n) (hp : p * p = p) :
    oddProjection p (evenProjection p x) = 0 := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  simp only [evenProjection_apply, oddProjection_apply, positive, negative, raise, lower,
    corner, complement]
  noncomm_ring [hp, hp_left]

theorem odd_eq_self_iff_tangent (p x : Mat n) (hp : p * p = p) :
    oddProjection p x = x ↔ x ∈ tangentSpace p := by
  rw [mem_tangentSpace, tangent_iff_odd_decomposition p x hp, oddProjection_apply, eq_comm]

/-- The odd projection has exactly the algebraic tangent space as its image. -/
theorem odd_isProj (p : Mat n) (hp : p * p = p) :
    LinearMap.IsProj (tangentSpace p) (oddProjection p) where
  map_mem x := (odd_eq_self_iff_tangent p _ hp).mp (odd_odd p x hp)
  map_id x hx := (odd_eq_self_iff_tangent p x hp).mpr hx

theorem range_odd_eq_tangentSpace (p : Mat n) (hp : p * p = p) :
    LinearMap.range (oddProjection p) = tangentSpace p := (odd_isProj p hp).range

/-- The even space is intrinsically the kernel of the odd projection. -/
def evenSpace (p : Mat n) : Submodule ℂ (Mat n) := LinearMap.ker (oddProjection p)

@[simp] theorem mem_evenSpace (p x : Mat n) :
    x ∈ evenSpace p ↔ oddProjection p x = 0 := Iff.rfl

theorem even_eq_self_iff (p x : Mat n) :
    evenProjection p x = x ↔ x ∈ evenSpace p := by
  rw [mem_evenSpace]
  have h := even_add_odd p x
  constructor
  · intro he
    rw [he] at h
    exact add_eq_left.mp h
  · intro ho
    simpa [ho] using h

theorem even_isProj (p : Mat n) (hp : p * p = p) :
    LinearMap.IsProj (evenSpace p) (evenProjection p) where
  map_mem x := (mem_evenSpace p _).mpr (odd_even p x hp)
  map_id x hx := (even_eq_self_iff p x).mpr hx

theorem range_even_eq_evenSpace (p : Mat n) (hp : p * p = p) :
    LinearMap.range (evenProjection p) = evenSpace p := (even_isProj p hp).range

/-- The tangent and even spaces are complementary native submodules. -/
theorem tangent_even_isCompl (p : Mat n) (hp : p * p = p) :
    IsCompl (tangentSpace p) (evenSpace p) := (odd_isProj p hp).isCompl

/-- Addition identifies the direct product of the two complementary spaces with all matrices. -/
def tangentEvenEquiv (p : Mat n) (hp : p * p = p) :
    (tangentSpace p × evenSpace p) ≃ₗ[ℂ] Mat n :=
  (tangentSpace p).prodEquivOfIsCompl (evenSpace p) (tangent_even_isCompl p hp)

@[simp] theorem tangentEvenEquiv_apply (p : Mat n) (hp : p * p = p)
    (x : tangentSpace p) (y : evenSpace p) :
    tangentEvenEquiv p hp (x, y) = (x : Mat n) + (y : Mat n) := rfl

/-- A complementary decomposition determines its two components uniquely. -/
theorem even_odd_decomposition_unique (p x e o : Mat n) (hp : p * p = p)
    (he : e ∈ evenSpace p) (ho : o ∈ tangentSpace p) (h : e + o = x) :
    e = evenProjection p x ∧ o = oddProjection p x := by
  have he' := (even_eq_self_iff p e).mpr he
  have ho' := (odd_eq_self_iff_tangent p o hp).mpr ho
  have he0 := (mem_evenSpace p e).mp he
  have ho0 : evenProjection p o = 0 := by
    rw [← ho']
    exact even_odd p o hp
  constructor
  · rw [← h, map_add, he', ho0, add_zero]
  · rw [← h, map_add, he0, ho', zero_add]

/-- The four components are recovered by the four native corner projections. -/
theorem four_corner_recovery (p a b c d : Mat n) (hp : p * p = p) :
    let x := positive p a + raise p b + lower p c + negative p d
    positive p x = positive p a ∧ raise p x = raise p b ∧
      lower p x = lower p c ∧ negative p x = negative p d := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [positive, negative, raise, lower, corner, complement] <;>
    noncomm_ring [hp, hp_left]

/-- Support in the four corners and the total sum uniquely determine every component. -/
theorem four_corner_unique (p x a b c d : Mat n) (hp : p * p = p)
    (ha : positive p a = a) (hb : raise p b = b)
    (hc : lower p c = c) (hd : negative p d = d) (hs : a + b + c + d = x) :
    positive p x = a ∧ raise p x = b ∧ lower p x = c ∧ negative p x = d := by
  have h := four_corner_recovery p a b c d hp
  simpa only [ha, hb, hc, hd, hs] using h

/-- Double commutation is the odd projection on all matrices, not only tangent vectors. -/
theorem double_commutator_eq_odd (p x : Mat n) (hp : p * p = p) :
    (x * p - p * x) * p - p * (x * p - p * x) = oddProjection p x := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  simp only [oddProjection_apply, raise, lower, corner, complement]
  noncomm_ring [hp, hp_left]

def tangentGenerator (p x : Mat n) : Mat n := x * p - p * x

theorem tangentGenerator_commutator (p x : Mat n) (hp : p * p = p)
    (hx : x ∈ tangentSpace p) :
    tangentGenerator p x * p - p * tangentGenerator p x = x :=
  tangent_commutator p x hp ((mem_tangentSpace p x).mp hx)

/-- All infinitesimal conjugations are tangent to the idempotent equation. -/
theorem commutator_mem_tangentSpace (p k : Mat n) (hp : p * p = p) :
    k * p - p * k ∈ tangentSpace p := by
  rw [mem_tangentSpace]
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  noncomm_ring [hp, hp_left]

theorem mem_tangentSpace_iff_commutator (p x : Mat n) (hp : p * p = p) :
    x ∈ tangentSpace p ↔ ∃ k : Mat n, k * p - p * k = x := by
  constructor
  · intro hx
    exact ⟨tangentGenerator p x, tangentGenerator_commutator p x hp hx⟩
  · rintro ⟨k, rfl⟩
    exact commutator_mem_tangentSpace p k hp

omit [DecidableEq n] in
/-- A Hermitian tangent vector has a canonical skew-Hermitian generator. -/
theorem tangentGenerator_skewHermitian (p x : Mat n)
    (hp : p.IsHermitian) (hx : x.IsHermitian) :
    (tangentGenerator p x)ᴴ = -(tangentGenerator p x) := by
  simp only [tangentGenerator, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hp.eq, hx.eq]
  abel

omit [DecidableEq n] in
/-- The commutator of a skew-Hermitian generator with a Hermitian idempotent is Hermitian. -/
theorem commutator_isHermitian (p k : Mat n) (hp : p.IsHermitian) (hk : kᴴ = -k) :
    (k * p - p * k).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hp.eq, hk]
  noncomm_ring

theorem hermitian_tangent_iff_skew_generator (p x : Mat n) (hp : p * p = p)
    (hps : p.IsHermitian) :
    x.IsHermitian ∧ x ∈ tangentSpace p ↔
      ∃ k : Mat n, kᴴ = -k ∧ k * p - p * k = x := by
  constructor
  · rintro ⟨hxs, hx⟩
    exact ⟨tangentGenerator p x, tangentGenerator_skewHermitian p x hps hxs,
      tangentGenerator_commutator p x hp hx⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨commutator_isHermitian p k hps hk, commutator_mem_tangentSpace p k hp⟩

end InfoGeometry.Canonical.MatrixPeirceZorn.MatrixGeometry
