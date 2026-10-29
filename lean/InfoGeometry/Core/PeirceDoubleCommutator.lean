/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanGenerators

/-!
# Squared native adjoint actions on an opposite-corner frame

The sum and difference of opposite Peirce corners have the quadratic operators
already owned by `PeirceQuadraticFrame`. Their squared adjoint actions retain
these operators as left factors. The resulting identities are equations in the
full associative algebra and its native endomorphism ring.
-/

namespace InfoGeometry.Core.PeirceDoubleCommutator

open PeirceDecomposition PeirceGrading PeirceCoupledCorners
open PeirceQuadraticFrame PeirceSandwichDuality LieJordanGenerators

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A squared inner action vanishes on the coefficient's commutant. -/
theorem ad_sq_apply_of_commute (a x : A) (hax : Commute a x) :
    (LieAlgebra.ad R A a ^ 2) x = 0 := by
  rw [pow_two]
  change a * (a * x - x * a) - (a * x - x * a) * a = 0
  rw [hax.eq, sub_self, mul_zero, zero_mul, sub_self]

/-- On an anticommuting element, the square retains the full coefficient square. -/
theorem ad_sq_apply_of_anticommute (a x : A) (hax : a * x + x * a = 0) :
    (LieAlgebra.ad R A a ^ 2) x = 4 • (a ^ 2 * x) := by
  have hxa : x * a = -(a * x) := by
    calc
      x * a = (a * x + x * a) - a * x := by abel
      _ = -(a * x) := by rw [hax, zero_sub]
  rw [pow_two, pow_two]
  change a * (a * x - x * a) - (a * x - x * a) * a =
    4 • ((a * a) * x)
  calc
    _ = a * (a * x + a * x) - (a * x + a * x) * a := by
      rw [hxa, sub_neg_eq_add]
    _ = (a * a) * x + (a * a) * x - (a * (x * a) + a * (x * a)) := by
      noncomm_ring
    _ = 4 • ((a * a) * x) := by
      rw [hxa]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      noncomm_ring

/-- The two signed squares sum to twice the existing symmetric generator. -/
theorem ad_sum_difference_trinity (u v : A) :
    -(LieAlgebra.ad R A (u + v) ^ 2) + LieAlgebra.ad R A (u - v) ^ 2 =
      2 • symmetricGenerator (R := R) u v := by
  simp only [map_add, map_sub, symmetricGenerator, two_nsmul]
  noncomm_ring

section OppositeCorners

variable {p u v : A}

/-- The sum's negative squared adjoint action annihilates the quadratic operator. -/
theorem neg_ad_sum_sq_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (u * v + v * u) = 0 := by
  rw [LinearMap.neg_apply, ad_sq_apply_of_commute (R := R) _ _
    (quadratic_commute_sum hp hu hv).symm, neg_zero]

/-- The sum itself is annihilated without any corner hypotheses. -/
theorem neg_ad_sum_sq_sum (u v : A) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (u + v) = 0 := by
  rw [LinearMap.neg_apply,
    ad_sq_apply_of_commute (R := R) _ _ (Commute.refl (u + v)), neg_zero]

/-- The difference retains the common quadratic operator as a left factor. -/
theorem neg_ad_sum_sq_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (u - v) =
      -(4 • ((u * v + v * u) * (u - v))) := by
  rw [LinearMap.neg_apply, ad_sq_apply_of_anticommute (R := R) _ _
    (sum_difference_anticommute hp hu hv), coupled_square hp hu hv]

/-- The corner bracket has the same quadratic left factor. -/
theorem neg_ad_sum_sq_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  have h : (u + v) * ⁅u, v⁆ + ⁅u, v⁆ * (u + v) = 0 := by
    simpa only [add_comm] using bracket_sum_anticommute hp hu hv
  rw [LinearMap.neg_apply, ad_sq_apply_of_anticommute (R := R) _ _ h,
    coupled_square hp hu hv]

/-- The grading reflection is an anticommuting input for the sum. -/
theorem neg_ad_sum_sq_reflection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad R A (u + v) ^ 2)) (reflection p) =
      -(4 • ((u * v + v * u) * reflection p)) := by
  have h : (u + v) * reflection p + reflection p * (u + v) = 0 := by
    simpa only [add_comm] using odd_anticommutes_reflection hp (coupled_odd hp hu hv)
  rw [LinearMap.neg_apply, ad_sq_apply_of_anticommute (R := R) _ _ h,
    coupled_square hp hu hv]

/-- The difference's squared adjoint action annihilates the quadratic operator. -/
theorem ad_difference_sq_quadratic (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) (u * v + v * u) = 0 :=
  ad_sq_apply_of_commute (R := R) _ _ (quadratic_commute_difference hp hu hv).symm

/-- The square of the difference coefficient supplies the negative sign. -/
theorem ad_difference_sq_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) (u + v) =
      -(4 • ((u * v + v * u) * (u + v))) := by
  have h : (u - v) * (u + v) + (u + v) * (u - v) = 0 := by
    simpa only [add_comm] using sum_difference_anticommute hp hu hv
  rw [ad_sq_apply_of_anticommute (R := R) _ _ h, difference_square hp hu hv,
    neg_mul, smul_neg]

/-- The difference itself is annihilated without any corner hypotheses. -/
theorem ad_difference_sq_difference (u v : A) :
    (LieAlgebra.ad R A (u - v) ^ 2) (u - v) = 0 :=
  ad_sq_apply_of_commute (R := R) _ _ (Commute.refl (u - v))

/-- The difference's squared adjoint action on the corner bracket. -/
theorem ad_difference_sq_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  have h : (u - v) * ⁅u, v⁆ + ⁅u, v⁆ * (u - v) = 0 := by
    simpa only [add_comm] using bracket_difference_anticommute hp hu hv
  rw [ad_sq_apply_of_anticommute (R := R) _ _ h, difference_square hp hu hv,
    neg_mul, smul_neg]

/-- The grading reflection is also an anticommuting input for the difference. -/
theorem ad_difference_sq_reflection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A (u - v) ^ 2) (reflection p) =
      -(4 • ((u * v + v * u) * reflection p)) := by
  have h : (u - v) * reflection p + reflection p * (u - v) = 0 := by
    simp only [sub_mul, mul_sub, corner10_mul_reflection hp hu,
      corner01_mul_reflection hp hv, reflection_mul_corner10 hp hu,
      reflection_mul_corner01 hp hv]
    abel
  rw [ad_sq_apply_of_anticommute (R := R) _ _ h, difference_square hp hu hv,
    neg_mul, smul_neg]

end OppositeCorners

end InfoGeometry.Core.PeirceDoubleCommutator
