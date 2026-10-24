/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceHyperbolicOrbit

/-! Complementary hyperbolic projections inside the existing active support. -/
namespace InfoGeometry.Canonical.PeirceHyperbolicComplement
open ReflexiveNilpotentFlows PeirceHyperbolicOrbit
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def hyperbolicMinus (u v : R) (d B : A) : A :=
  support d B - hyperbolicPlus u v d B

theorem hyperbolic_sum (u v : R) (d B : A) :
    hyperbolicPlus u v d B + hyperbolicMinus u v d B = support d B := by
  unfold hyperbolicMinus
  abel

theorem hyperbolicMinus_expansion (u v : R) (h : u*u-v*v=1) (d B : A) :
    hyperbolicMinus u v d B =
      -(v*v) • (d*B) + (u*u) • (B*d) + (u*v) • (d-B) := by
  have hu : u*u=1+v*v := by linear_combination h
  rw [hyperbolicMinus, hyperbolicPlus_expansion, hu]
  simp only [support, add_smul, one_smul, neg_smul]
  abel

variable {d B : A} (hd : d*d=0) (hB : B*B=0)
  (hr : d*B*d=d) (hs : B*d*B=B)
include hd hB hr hs

theorem support_mul_hyperbolicPlus (u v : R) :
    support d B * hyperbolicPlus u v d B = hyperbolicPlus u v d B := by
  rw [hyperbolicPlus, ← pairMatrixLinear_one (R := R),
    ← pairMatrixLinear_mul hd hB hr hs, one_mul]

theorem hyperbolicPlus_mul_support (u v : R) :
    hyperbolicPlus u v d B * support d B = hyperbolicPlus u v d B := by
  rw [hyperbolicPlus, ← pairMatrixLinear_one (R := R),
    ← pairMatrixLinear_mul hd hB hr hs, mul_one]

theorem hyperbolicMinus_idempotent (u v : R) (h : u*u-v*v=1) :
    IsIdempotentElem (hyperbolicMinus u v d B) := by
  change (support d B-hyperbolicPlus u v d B)*
    (support d B-hyperbolicPlus u v d B)=support d B-hyperbolicPlus u v d B
  rw [sub_mul, mul_sub, mul_sub, support_sq hd hB hr hs,
    support_mul_hyperbolicPlus hd hB hr hs, hyperbolicPlus_mul_support hd hB hr hs,
    (hyperbolicPlus_idempotent hd hB hr hs u v h).eq]
  abel

theorem hyperbolic_orthogonal (u v : R) (h : u*u-v*v=1) :
    hyperbolicPlus u v d B * hyperbolicMinus u v d B = 0 ∧
    hyperbolicMinus u v d B * hyperbolicPlus u v d B = 0 := by
  unfold hyperbolicMinus
  rw [mul_sub, sub_mul, support_mul_hyperbolicPlus hd hB hr hs,
    hyperbolicPlus_mul_support hd hB hr hs,
    (hyperbolicPlus_idempotent hd hB hr hs u v h).eq, sub_self]
  exact ⟨rfl, rfl⟩

end InfoGeometry.Canonical.PeirceHyperbolicComplement
