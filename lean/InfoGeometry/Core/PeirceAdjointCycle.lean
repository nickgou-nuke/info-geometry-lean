/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners

/-!
# Native adjoint geometry of an idempotent

The square of the native adjoint endomorphism is the existing integer-linear
odd projection. Its range is the odd sector and its kernel is the even sector.
The two supported corners have opposite adjoint actions, with no restriction
on the characteristic and no claim that the cubic polynomial is minimal.
-/

namespace InfoGeometry.Core.PeirceAdjointCycle

attribute [local instance 100] LieRing.ofAssociativeRing

open PeirceDecomposition PeirceGrading PeirceCoupledCorners

variable {A : Type*} [Ring A] {p u v : A}

/-- Native bundling of the owned double-commutator reconstruction. -/
theorem ad_sq_eq_odd (hp : IsIdempotentElem p) :
    LieAlgebra.ad ℤ A p ^ 2 = odd p := by
  apply LinearMap.ext
  intro x
  change p * (p * x - x * p) - (p * x - x * p) * p = odd p x
  exact (odd_reconstruction hp x).2.symm

/-- This is an annihilating polynomial, with no minimality assertion. -/
theorem ad_cube_eq_ad (hp : IsIdempotentElem p) :
    LieAlgebra.ad ℤ A p ^ 3 = LieAlgebra.ad ℤ A p := by
  rw [pow_succ, ad_sq_eq_odd hp]
  apply LinearMap.ext
  intro x
  change odd p (p * x - x * p) = p * x - x * p
  exact (LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp)).mp
    (commutator_odd hp x)

theorem ad_range_eq_odd_range (hp : IsIdempotentElem p) :
    LinearMap.range (LieAlgebra.ad ℤ A p) = LinearMap.range (odd p) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact commutator_odd hp y
  · intro hx
    refine ⟨LieAlgebra.ad ℤ A p x, ?_⟩
    calc
      LieAlgebra.ad ℤ A p (LieAlgebra.ad ℤ A p x) = odd p x :=
        (odd_reconstruction hp x).2.symm
      _ = x := (LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp)).mp hx

theorem ad_ker_eq_even_range (hp : IsIdempotentElem p) :
    LinearMap.ker (LieAlgebra.ad ℤ A p) = LinearMap.range (even p) := by
  ext x
  rw [LinearMap.mem_ker, mem_even_iff hp]
  change p * x - x * p = 0 ↔ p * x = x * p
  exact sub_eq_zero

/-- The adjoint action is involutive on the actual odd range. -/
theorem ad_twice_of_mem_odd (hp : IsIdempotentElem p) {x : A}
    (hx : x ∈ LinearMap.range (odd p)) :
    LieAlgebra.ad ℤ A p (LieAlgebra.ad ℤ A p x) = x := by
  calc
    LieAlgebra.ad ℤ A p (LieAlgebra.ad ℤ A p x) = odd p x :=
      (odd_reconstruction hp x).2.symm
    _ = x := (LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp)).mp hx

/-- The first directed corner is extracted from the commutator by left support. -/
theorem left_mul_commutator (hp : IsIdempotentElem p) (x : A) :
    p * ⁅p, x⁆ = component10 p x := by
  change p * (p * x - x * p) = p * x * (1 - p)
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- The opposite directed corner has the negative right-support convention. -/
theorem neg_commutator_mul (hp : IsIdempotentElem p) (x : A) :
    -(⁅p, x⁆ * p) = component01 p x := by
  change -((p * x - x * p) * p) = (1 - p) * x * p
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem ad_eq_self_of_mem10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    LieAlgebra.ad ℤ A p u = u := by
  change p * u - u * p = u
  rw [left_support10 hp hu, right_support10 hp hu, sub_zero]

theorem ad_eq_neg_of_mem01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    LieAlgebra.ad ℤ A p v = -v := by
  change p * v - v * p = -v
  rw [left_support01 hp hv, right_support01 hp hv, zero_sub]

theorem ad_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LieAlgebra.ad ℤ A p (u + v) = u - v := by
  rw [map_add, ad_eq_self_of_mem10 hp hu, ad_eq_neg_of_mem01 hp hv, sub_eq_add_neg]

theorem ad_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LieAlgebra.ad ℤ A p (u - v) = u + v := by
  rw [map_sub, ad_eq_self_of_mem10 hp hu, ad_eq_neg_of_mem01 hp hv, sub_neg_eq_add]

theorem ad_commutator_eq_odd (hp : IsIdempotentElem p) (x : A) :
    LieAlgebra.ad ℤ A p ⁅p, x⁆ = odd p x :=
  (odd_reconstruction hp x).2.symm

theorem ad_odd_eq_ad (hp : IsIdempotentElem p) (x : A) :
    LieAlgebra.ad ℤ A p (odd p x) = LieAlgebra.ad ℤ A p x := by
  have h := congrArg (fun f : Module.End ℤ A => f x) (ad_cube_eq_ad hp)
  change LieAlgebra.ad ℤ A p (LieAlgebra.ad ℤ A p (LieAlgebra.ad ℤ A p x)) =
    LieAlgebra.ad ℤ A p x at h
  rw [(odd_reconstruction hp x).2]
  exact h

end InfoGeometry.Core.PeirceAdjointCycle
