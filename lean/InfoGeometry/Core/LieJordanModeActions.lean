/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanGenerators
import InfoGeometry.Core.SquareZeroSandwich
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Square-zero modes of the native Lie–Jordan generators

Each square-zero seed is annihilated by the signed sandwich and by both
mixed generators, independently of the other seed. Their native joint kernel
therefore contains the span of the pair. The sum and difference have the same
symmetric-generator coefficient, as supplied by the existing full-matrix
square-zero sandwich owner.
-/

namespace InfoGeometry.Core.LieJordanModeActions

open JordanMultiplicationClosure LieJordanBoundaryOperators LieJordanGenerators

attribute [local instance 100] LieRing.ofAssociativeRing

section Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {u v : A}

local notation "D" => LieAlgebra.ad R A
local notation "J" => jordanLeft (R := R)

/-- The signed sandwich kills a square-zero first seed. -/
theorem signed_sandwich_left (hu : u * u = 0) :
    (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)) u = 0 := by
  change u * u * v - v * u * u = 0
  rw [hu, zero_mul, mul_assoc, hu, mul_zero, sub_self]

/-- The second seed only needs its own square-zero equation. -/
theorem signed_sandwich_right (hv : v * v = 0) :
    (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)) v = 0 := by
  change u * v * v - v * v * u = 0
  rw [hv, zero_mul, mul_assoc, hv, mul_zero, sub_self]

/-- The existing zero mixed composition gives the first skew-plus zero mode. -/
theorem skewPlusGenerator_left (hu : u * u = 0) :
    skewPlusGenerator (R := R) u v u = 0 := by
  have hzero : D u (J u v) = 0 :=
    congrArg (fun T : Module.End R A => T v) (ad_mul_jordan_eq_zero (R := R) hu)
  have hsymm : J v u = J u v := add_comm _ _
  have hself : J u u = 0 := by
    change u * u + u * u = 0
    simp only [hu, add_zero]
  rw [skewPlusGenerator_apply, hsymm, hzero, hself, map_zero, sub_self]

theorem skewPlusGenerator_right (hv : v * v = 0) :
    skewPlusGenerator (R := R) u v v = 0 := by
  have hzero : D v (J v u) = 0 :=
    congrArg (fun T : Module.End R A => T u) (ad_mul_jordan_eq_zero (R := R) hv)
  have hsymm : J u v = J v u := add_comm _ _
  have hself : J v v = 0 := by
    change v * v + v * v = 0
    simp only [hv, add_zero]
  rw [skewPlusGenerator_apply, hself, map_zero, hsymm, hzero, sub_self]

/-- The opposite zero mixed composition gives the skew-minus zero mode. -/
theorem skewMinusGenerator_left (hu : u * u = 0) :
    skewMinusGenerator (R := R) u v u = 0 := by
  have hzero : J u (D u v) = 0 :=
    congrArg (fun T : Module.End R A => T v) (jordan_mul_ad_eq_zero (R := R) hu)
  have hskew : D v u = -(D u v) := (lie_skew v u).symm
  rw [skewMinusGenerator_apply, hskew, map_neg, hzero]
  simp only [LieAlgebra.ad_apply, lie_self, map_zero, neg_zero, sub_self]

theorem skewMinusGenerator_right (hv : v * v = 0) :
    skewMinusGenerator (R := R) u v v = 0 := by
  have hzero : J v (D v u) = 0 :=
    congrArg (fun T : Module.End R A => T u) (jordan_mul_ad_eq_zero (R := R) hv)
  have hskew : D u v = -(D v u) := (lie_skew u v).symm
  rw [skewMinusGenerator_apply, hskew, map_neg, hzero]
  simp only [LieAlgebra.ad_apply, lie_self, map_zero, neg_zero, sub_self]

theorem signed_sandwich_sum (hu : u * u = 0) (hv : v * v = 0) :
    (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)) (u + v) = 0 := by
  rw [map_add, signed_sandwich_left hu, signed_sandwich_right hv, add_zero]

theorem signed_sandwich_difference (hu : u * u = 0) (hv : v * v = 0) :
    (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)) (u - v) = 0 := by
  rw [map_sub, signed_sandwich_left hu, signed_sandwich_right hv, sub_self]

theorem skewPlusGenerator_sum (hu : u * u = 0) (hv : v * v = 0) :
    skewPlusGenerator (R := R) u v (u + v) = 0 := by
  rw [map_add, skewPlusGenerator_left hu, skewPlusGenerator_right hv, add_zero]

theorem skewPlusGenerator_difference (hu : u * u = 0) (hv : v * v = 0) :
    skewPlusGenerator (R := R) u v (u - v) = 0 := by
  rw [map_sub, skewPlusGenerator_left hu, skewPlusGenerator_right hv, sub_self]

theorem skewMinusGenerator_sum (hu : u * u = 0) (hv : v * v = 0) :
    skewMinusGenerator (R := R) u v (u + v) = 0 := by
  rw [map_add, skewMinusGenerator_left hu, skewMinusGenerator_right hv, add_zero]

theorem skewMinusGenerator_difference (hu : u * u = 0) (hv : v * v = 0) :
    skewMinusGenerator (R := R) u v (u - v) = 0 := by
  rw [map_sub, skewMinusGenerator_left hu, skewMinusGenerator_right hv, sub_self]

/-- The entire native span is stationary for all three signed actions. -/
theorem span_pair_le_common_kernel (hu : u * u = 0) (hv : v * v = 0) :
    Submodule.span R ({u, v} : Set A) ≤
      (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)).ker ⊓
        ((skewPlusGenerator (R := R) u v).ker ⊓
          (skewMinusGenerator (R := R) u v).ker) := by
  apply Submodule.span_le.mpr
  intro x hx
  change
    (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)) x = 0 ∧
      skewPlusGenerator (R := R) u v x = 0 ∧
        skewMinusGenerator (R := R) u v x = 0
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ⟨signed_sandwich_left hu, skewPlusGenerator_left hu, skewMinusGenerator_left hu⟩
  · have hxv : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨signed_sandwich_right hv, skewPlusGenerator_right hv, skewMinusGenerator_right hv⟩

end Algebra

section Matrices

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The existing full-matrix dissipator is the canonical native generator. -/
theorem symmDissipator_eq_symmetricGenerator (u v : Matrix n n R) :
    SquareZeroSandwich.symmDissipator u v = symmetricGenerator (R := R) u v := by
  apply LinearMap.ext
  intro x
  exact SquareZeroSandwich.dissipator_eq_double_commutator u v x

variable {u v : Matrix n n R}

/-- The native symmetric sandwich readout consumes the existing sum theorem. -/
theorem symmetric_sandwich_sum (hu : u * u = 0) (hv : v * v = 0) :
    (LinearMap.mulLeftRight R (u, v) + LinearMap.mulLeftRight R (v, u)) (u + v) = 0 := by
  exact SquareZeroSandwich.sandwich_add hu hv

theorem symmetric_sandwich_difference (hu : u * u = 0) (hv : v * v = 0) :
    (LinearMap.mulLeftRight R (u, v) + LinearMap.mulLeftRight R (v, u)) (u - v) = 0 := by
  exact SquareZeroSandwich.sandwich_sub hu hv

/-- The sum has the existing operator-valued coefficient minus twice the quadratic product. -/
theorem symmetricGenerator_sum (hu : u * u = 0) (hv : v * v = 0) :
    symmetricGenerator (R := R) u v (u + v) =
      -((2 : R) • ((u * v + v * u) * (u + v))) := by
  simpa only [symmDissipator_eq_symmetricGenerator] using
    (SquareZeroSandwich.dissipator_add hu hv)

/-- The difference has the same operator-valued coefficient as the sum. -/
theorem symmetricGenerator_difference (hu : u * u = 0) (hv : v * v = 0) :
    symmetricGenerator (R := R) u v (u - v) =
      -((2 : R) • ((u * v + v * u) * (u - v))) := by
  simpa only [symmDissipator_eq_symmetricGenerator] using
    (SquareZeroSandwich.dissipator_sub hu hv)

end Matrices

end InfoGeometry.Core.LieJordanModeActions
