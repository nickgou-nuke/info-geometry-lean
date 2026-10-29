/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanGenerators

/-!
# Single adjoint squares on the Peirce quadratic frame

The two operators are the negative adjoint square of the corner sum and the
positive adjoint square of the corner difference. They are written directly
as native endomorphisms. Their sum is twice the existing paired symmetric
generator. The action table retains the quadratic element as a left operator
factor, and all naturality statements use native algebra homomorphisms.
-/

namespace InfoGeometry.Core.LieJordanSingleSquare

attribute [local instance 100] LieRing.ofAssociativeRing

open LieJordanBoundaryOperators LieJordanGenerators
open PeirceDecomposition PeirceCoupledCorners PeirceQuadraticFrame

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Anticommutation determines the adjoint square without dividing by two. -/
theorem ad_sq_apply_of_anticommute (a x : A) (h : a * x + x * a = 0) :
    (LieAlgebra.ad R A a ^ 2) x = 4 • ((a * a) * x) := by
  have hxa : x * a = -(a * x) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using h
  have haxa : a * x * a = -((a * a) * x) := by
    calc
      a * x * a = a * (x * a) := mul_assoc a x a
      _ = a * (-(a * x)) := by rw [hxa]
      _ = -((a * a) * x) := by rw [mul_neg, ← mul_assoc]
  have hxaa : x * (a * a) = (a * a) * x := by
    calc
      x * (a * a) = (x * a) * a := (mul_assoc x a a).symm
      _ = -(a * x * a) := by rw [hxa, neg_mul]
      _ = (a * a) * x := by rw [haxa, neg_neg]
  rw [ad_sq, two_nsmul]
  change (a * a) * x + x * (a * a) - (a * x * a + a * x * a) =
    4 • ((a * a) * x)
  simp only [haxa, hxaa]
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]
  abel

/-- The relation with the paired generator needs no corner hypotheses. -/
theorem single_squares_add (u v : A) :
    -(LieAlgebra.ad R A (u + v) ^ 2) +
        LieAlgebra.ad R A (u - v) ^ 2 =
      2 • symmetricGenerator (R := R) u v := by
  rw [map_add, map_sub, symmetricGenerator]
  simp only [pow_two, two_nsmul]
  noncomm_ring

@[simp] theorem neg_ad_sum_sq_one (u v : A) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) 1 = 0 := by
  simp only [LinearMap.neg_apply, pow_two, Module.End.mul_apply,
    LieAlgebra.ad_apply, Ring.lie_def, mul_one, one_mul, sub_self,
    mul_zero, zero_mul, neg_zero]

@[simp] theorem ad_sub_sq_one (u v : A) :
    (LieAlgebra.ad R A (u - v) ^ 2) 1 = 0 := by
  simp only [pow_two, Module.End.mul_apply, LieAlgebra.ad_apply,
    Ring.lie_def, mul_one, one_mul, sub_self, mul_zero, zero_mul]

@[simp] theorem neg_ad_sum_sq_sum (u v : A) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (u + v) = 0 := by
  simp only [LinearMap.neg_apply, pow_two, Module.End.mul_apply,
    LieAlgebra.ad_apply, lie_self, lie_zero, neg_zero]

@[simp] theorem ad_sub_sq_sub (u v : A) :
    (LieAlgebra.ad R A (u - v) ^ 2) (u - v) = 0 := by
  simp only [pow_two, Module.End.mul_apply, LieAlgebra.ad_apply,
    lie_self, lie_zero]

section OppositeCorners

variable {p u v : A}

theorem neg_ad_sum_sq_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (u * v + v * u) = 0 := by
  have hK : LieAlgebra.ad R A (u + v) (u * v + v * u) = 0 := by
    change (u + v) * (u * v + v * u) - (u * v + v * u) * (u + v) = 0
    exact sub_eq_zero.mpr (quadratic_commute_sum hp hu hv).symm.eq
  simp only [LinearMap.neg_apply, pow_two, Module.End.mul_apply,
    hK, map_zero, neg_zero]

theorem ad_sub_sq_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) (u * v + v * u) = 0 := by
  have hK : LieAlgebra.ad R A (u - v) (u * v + v * u) = 0 := by
    change (u - v) * (u * v + v * u) - (u * v + v * u) * (u - v) = 0
    exact sub_eq_zero.mpr (quadratic_commute_difference hp hu hv).symm.eq
  simp only [pow_two, Module.End.mul_apply, hK, map_zero]

theorem neg_ad_sum_sq_sub (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (u - v) =
      -(4 • ((u * v + v * u) * (u - v))) := by
  rw [LinearMap.neg_apply,
    ad_sq_apply_of_anticommute (R := R) (u + v) (u - v)
      (sum_difference_anticommute hp hu hv),
    ← pow_two, coupled_square hp hu hv]

theorem ad_sub_sq_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) (u + v) =
      -(4 • ((u * v + v * u) * (u + v))) := by
  have hanti : (u - v) * (u + v) + (u + v) * (u - v) = 0 := by
    simpa only [add_comm] using sum_difference_anticommute hp hu hv
  rw [ad_sq_apply_of_anticommute (R := R) (u - v) (u + v) hanti,
    ← pow_two, difference_square hp hu hv, neg_mul, smul_neg]

theorem neg_ad_sum_sq_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  have hanti : (u + v) * ⁅u, v⁆ + ⁅u, v⁆ * (u + v) = 0 := by
    simpa only [add_comm] using bracket_sum_anticommute hp hu hv
  rw [LinearMap.neg_apply,
    ad_sq_apply_of_anticommute (R := R) (u + v) ⁅u, v⁆ hanti,
    ← pow_two, coupled_square hp hu hv]

theorem ad_sub_sq_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  have hanti : (u - v) * ⁅u, v⁆ + ⁅u, v⁆ * (u - v) = 0 := by
    simpa only [add_comm] using bracket_difference_anticommute hp hu hv
  rw [ad_sq_apply_of_anticommute (R := R) (u - v) ⁅u, v⁆ hanti,
    ← pow_two, difference_square hp hu hv, neg_mul, smul_neg]

end OppositeCorners

section Naturality

variable {B : Type*} [Ring B] [Algebra R B]

/-- A native algebra homomorphism intertwines every individual adjoint square. -/
theorem map_ad_sq_apply (f : A →ₐ[R] B) (a x : A) :
    f ((LieAlgebra.ad R A a ^ 2) x) =
      (LieAlgebra.ad R B (f a) ^ 2) (f x) := by
  simp only [pow_two, Module.End.mul_apply, LieAlgebra.ad_apply]
  change f.toLieHom ⁅a, ⁅a, x⁆⁆ =
    ⁅f.toLieHom a, ⁅f.toLieHom a, f.toLieHom x⁆⁆
  simp only [LieHom.map_lie]

theorem map_neg_ad_sum_sq (f : A →ₐ[R] B) (u v x : A) :
    f ((-(LieAlgebra.ad R A (u + v) ^ 2)) x) =
      (-(LieAlgebra.ad R B (f u + f v) ^ 2)) (f x) := by
  simpa only [LinearMap.neg_apply, map_neg, map_add] using
    congrArg (fun y : B => -y) (map_ad_sq_apply f (u + v) x)

theorem map_ad_sub_sq (f : A →ₐ[R] B) (u v x : A) :
    f ((LieAlgebra.ad R A (u - v) ^ 2) x) =
      (LieAlgebra.ad R B (f u - f v) ^ 2) (f x) := by
  simpa only [map_sub] using map_ad_sq_apply f (u - v) x

/-- Naturality as an equality of native linear-map compositions. -/
theorem comp_neg_ad_sum_sq (f : A →ₐ[R] B) (u v : A) :
    f.toLinearMap.comp (-(LieAlgebra.ad R A (u + v) ^ 2)) =
      (-(LieAlgebra.ad R B (f u + f v) ^ 2)).comp f.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact map_neg_ad_sum_sq f u v x

theorem comp_ad_sub_sq (f : A →ₐ[R] B) (u v : A) :
    f.toLinearMap.comp (LieAlgebra.ad R A (u - v) ^ 2) =
      (LieAlgebra.ad R B (f u - f v) ^ 2).comp f.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact map_ad_sub_sq f u v x

end Naturality

end InfoGeometry.Core.LieJordanSingleSquare
