/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import InfoGeometry.OperatorAlgebra.TracialCARDensity
import InfoGeometry.Core.JordanAssociatorRing

/-!
# Peirce projections, common kernels and weighted trace identities

The carrier is an associative algebra. The pair is explicitly square-zero and
reflexive; no existence of a Moore–Penrose inverse is asserted. The complement
is characterized on the left regular module, not as an elliptic Hodge theorem.
Weighted functionals use the existing tracial owner, with no positivity,
normalization, analytic KMS, or exceptional-Lie-algebra claim.

The Jordan–Lie archetype is owned by `JordanAssociatorRing`:
`symm_operator_commutator` has inner bracket `[s,t]`, not `[t,s]`.
The cyclotomic and Weyl archetypes remain in the imported owners; involutivity
is not the second cyclotomic equation, and fourth power one is not exact order four.
-/
namespace InfoGeometry.Canonical.PeirceWeightedTrace
open ReflexiveNilpotentFlows
open InfoGeometry.OperatorAlgebra.TracialCARDensity
open InfoGeometry.NCG

variable {A : Type*} [Ring A]

/-- The complement projects precisely onto the common kernel of left
multiplication by the two generators, on the regular module. -/
theorem complement_fixed_iff {d B : A}
    (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B) (x : A) :
    complement d B * x = x ↔ d*x=0 ∧ B*x=0 := by
  obtain ⟨_,hdH,_,hBH⟩ := complement_annihilates hd hB hr hs
  constructor
  · intro hx
    constructor
    · calc d*x = d*(complement d B*x) := congrArg (d * ·) hx.symm
           _ = 0 := by rw [← mul_assoc,hdH,zero_mul]
    · calc B*x = B*(complement d B*x) := congrArg (B * ·) hx.symm
           _ = 0 := by rw [← mul_assoc,hBH,zero_mul]
  · rintro ⟨hx,hy⟩
    simp only [complement,support,sub_mul,one_mul,add_mul,mul_assoc,
      hx,hy,mul_zero,add_zero,sub_zero]

/-- Self-adjointness of the support and its complement needs explicit
self-adjointness of the two products, not an assumed Hodge interpretation. -/
theorem support_complement_selfAdjoint [StarRing A] {d B : A}
    (hp : star (d*B)=d*B) (hm : star (B*d)=B*d) :
    star (support d B)=support d B ∧ star (complement d B)=complement d B := by
  simp only [support,complement,star_add,star_sub,star_one,hp,hm,and_self]

section Scalar
variable {R : Type*} [CommRing R] [Algebra R A]

/-- Active-support weight. The complement has coefficient zero; unlike a
full CAR pair, the active support need not be the ambient identity. -/
def supportWeight (a b : R) (d B : A) : A := a • (B*d) + b • (d*B)

/-- Four eigenproduct equations, without invertibility or positivity of weights. -/
theorem weight_eigenproducts {d B : A}
    (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B) (a b : R) :
    supportWeight a b d B*d=b • d ∧ d*supportWeight a b d B=a • d ∧
    supportWeight a b d B*B=a • B ∧ B*supportWeight a b d B=b • B := by
  have hr' : d*(B*d)=d := by simpa only [mul_assoc] using hr
  have hs' : B*(d*B)=B := by simpa only [mul_assoc] using hs
  have hdd : d*(d*B)=0 := by rw [← mul_assoc,hd,zero_mul]
  have hbb : B*(B*d)=0 := by rw [← mul_assoc,hB,zero_mul]
  simp only [supportWeight,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    mul_assoc,hd,hB,hr',hs',hdd,hbb,mul_zero,smul_zero,zero_add,add_zero,and_self]

/-- Division-free intertwining; squared weights are a specialization. -/
theorem weight_intertwining {d B : A}
    (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B) (a b : R) :
    a • (supportWeight a b d B*d)=b • (d*supportWeight a b d B) ∧
    b • (supportWeight a b d B*B)=a • (B*supportWeight a b d B) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := weight_eigenproducts hd hB hr hs a b
  simp only [h₁,h₂,h₃,h₄,smul_smul,mul_comm,and_self]

/-- Both weighted trace boundary laws follow from the existing generic
tracial eigenproduct theorem, with no analytic modular assumptions. -/
theorem weighted_trace_boundary (τ : TracialFunctional R A) {d B : A}
    (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B) (a b : R) (x : A) :
    a * weighted τ (supportWeight a b d B) (d*x) =
      b * weighted τ (supportWeight a b d B) (x*d) ∧
    b * weighted τ (supportWeight a b d B) (B*x) =
      a * weighted τ (supportWeight a b d B) (x*B) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := weight_eigenproducts hd hB hr hs a b
  exact ⟨eigenproductKMS τ _ d x b a h₁ h₂,
    eigenproductKMS τ _ B x a b h₃ h₄⟩
end Scalar
end InfoGeometry.Canonical.PeirceWeightedTrace
