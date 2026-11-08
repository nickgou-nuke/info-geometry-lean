/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.Tactic.Ring

/-!
# Finite subgroup averaging and binary character compression

The projection is Mathlib's actual `Representation.averageMap` for the right
regular representation restricted to a finite subgroup. Its image consists
exactly of functions on the coset quotient. Multiplication by a character
trivial on the subgroup preserves that image; a character nontrivial on the
subgroup has zero compressed first moment. An order-two character has an
exact second compression defect `b² • P`.

No normality is needed for the coset-space statements. Normality is required
only for the quotient to carry its native group structure. The vanishing of
one diagonal corner does not assert that the opposite corner vanishes, and
nonzero variance is stated with its exact nonzero coefficient condition.
-/

noncomputable section

namespace InfoGeometry.Algebra.SubgroupCompressionVariance

open TannakaDuality.FiniteGroup
open InfoGeometry.Core.PeirceCompressionDefect

universe u

section SubgroupAverage

variable {k G : Type u} [Field k] [Group G]
variable (H : Subgroup G) [Fintype H] [Invertible (Fintype.card H : k)]

local notation "ρH" => MonoidHom.comp (rightRegular (k := k) (G := G)) (Subgroup.subtype H)
local notation "P" => Representation.averageMap ρH

/-- Evaluation of the native averaging map is the normalized subgroup sum. -/
theorem subgroupAverage_apply (f : G → k) (x : G) :
    P f x = ⅟(Fintype.card H : k) * ∑ h : H, f (x * (h : G)) := by
  simp [Representation.averageMap, GroupAlgebra.average, map_sum,
    MonoidAlgebra.of_apply, rightRegular_apply]

/-- Idempotence is derived from the finite subgroup average. -/
theorem subgroupAverage_idempotent : P * P = P :=
  (Representation.isProj_averageMap ρH).isIdempotentElem.eq

/-- The average is constant on each right multiplication orbit of `H`. -/
theorem subgroupAverage_right_invariant (f : G → k) (h : H) (x : G) :
    P f (x * (h : G)) = P f x :=
  congrFun (Representation.averageMap_invariant ρH f h) x

/-- The image consists exactly of functions constant on right `H`-orbits. -/
theorem mem_subgroupAverage_range_iff (f : G → k) :
    f ∈ LinearMap.range P ↔ ∀ h : H, ∀ x : G, f (x * (h : G)) = f x := by
  rw [(Representation.isProj_averageMap ρH).range, Representation.mem_invariants]
  constructor
  · intro hf h x
    exact congrFun (hf h) x
  · intro hf h
    exact funext (hf h)

/-- The range is literally the pullback of functions on the native coset
quotient, rather than an abstractly assumed quotient projector. -/
theorem mem_subgroupAverage_range_iff_descends (f : G → k) :
    f ∈ LinearMap.range P ↔
      ∃ F : G ⧸ H → k, ∀ x : G, F (QuotientGroup.mk x) = f x := by
  rw [mem_subgroupAverage_range_iff]
  constructor
  · intro hf
    have hwell : ∀ a b : G, QuotientGroup.leftRel H a b → f a = f b := by
      intro a b hab
      have hm : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      simpa using (hf ⟨a⁻¹ * b, hm⟩ a).symm
    exact ⟨Quotient.lift f hwell, fun _ => rfl⟩
  · rintro ⟨F, hF⟩ h x
    rw [← hF (x * (h : G)), ← hF x,
      QuotientGroup.mk_mul_of_mem x h.property]

/-- Constants survive averaging, so this projection is nonzero. -/
theorem subgroupAverage_ne_zero : P ≠ 0 := by
  intro hz
  have hc : P (fun _ : G => (1 : k)) = fun _ => (1 : k) := by
    apply Representation.averageMap_id ρH
    intro h
    rfl
  have hone := congrFun hc (1 : G)
  rw [hz] at hone
  exact zero_ne_one hone

omit [Invertible (Fintype.card H : k)] in
/-- A nontrivial multiplicative character has zero sum on the subgroup. -/
theorem subgroup_character_sum_eq_zero (χ : G →* k)
    (hχ : ∃ h : H, χ (h : G) ≠ 1) : ∑ h : H, χ (h : G) = 0 := by
  obtain ⟨h, hh⟩ := hχ
  apply eq_zero_of_mul_eq_self_left hh
  rw [Finset.mul_sum]
  simpa only [← map_mul, ← Subgroup.coe_mul] using
    (Function.Bijective.sum_comp (Group.mulLeft_bijective h)
      (fun t : H => χ (t : G)))

/-- Exact compression formula for the native character multiplication map. -/
theorem subgroupAverage_character_sandwich (χ : G →* k) :
    P * LinearMap.mulLeft k (χ : G → k) * P =
      (⅟(Fintype.card H : k) * ∑ h : H, χ (h : G)) •
        (LinearMap.mulLeft k (χ : G → k) * P) := by
  ext f x
  change P (fun y => χ y * P f y) x =
    (⅟(Fintype.card H : k) * ∑ h : H, χ (h : G)) * (χ x * P f x)
  rw [subgroupAverage_apply]
  simp_rw [map_mul, subgroupAverage_right_invariant]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Characters nontrivial on the subgroup have zero compressed first moment. -/
theorem subgroupAverage_character_micro (χ : G →* k)
    (hχ : ∃ h : H, χ (h : G) ≠ 1) :
    P * LinearMap.mulLeft k (χ : G → k) * P = 0 := by
  rw [subgroupAverage_character_sandwich,
    subgroup_character_sum_eq_zero H χ hχ, mul_zero, zero_smul]

/-- Multiplication by a character constant on the subgroup commutes with the
actual averaging operator. -/
theorem subgroupAverage_character_commute (χ : G →* k)
    (hχ : ∀ h : H, χ (h : G) = 1) :
    P * LinearMap.mulLeft k (χ : G → k) =
      LinearMap.mulLeft k (χ : G → k) * P := by
  ext f x
  change P (fun y => χ y * f y) x = χ x * P f x
  rw [subgroupAverage_apply, subgroupAverage_apply]
  simp_rw [map_mul, hχ, mul_one]
  rw [← Finset.mul_sum]
  ring

/-- Characters trivial on the subgroup descend unchanged on the invariant range. -/
theorem subgroupAverage_character_macro (χ : G →* k)
    (hχ : ∀ h : H, χ (h : G) = 1) :
    P * LinearMap.mulLeft k (χ : G → k) * P =
      LinearMap.mulLeft k (χ : G → k) * P := by
  rw [subgroupAverage_character_sandwich]
  simp only [hχ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    invOf_mul_self, one_smul]

omit [Fintype H] [Invertible (Fintype.card H : k)] in
/-- Triviality on a normal subgroup supplies an actual descended character on
`G ⧸ H` through Mathlib's quotient universal property. -/
theorem character_descends_iff [H.Normal] (χ : G →* k) :
    (∀ h : H, χ (h : G) = 1) ↔
      ∃ ψ : G ⧸ H →* k, ψ.comp (QuotientGroup.mk' H) = χ := by
  constructor
  · intro hχ
    have hker : H ≤ χ.ker := fun h hh => hχ ⟨h, hh⟩
    exact ⟨QuotientGroup.lift H χ hker, by ext x; rfl⟩
  · rintro ⟨ψ, hψ⟩ h
    have heq := DFunLike.congr_fun hψ (h : G)
    have hquot : QuotientGroup.mk' H (h : G) = 1 :=
      (QuotientGroup.eq_one_iff (h : G)).mpr h.property
    simpa only [MonoidHom.comp_apply, hquot, map_one] using heq.symm

end SubgroupAverage

section AlgebraicCompression

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- The binary normal form is preserved on the macro corner. -/
theorem binary_macro_compression (p σ : A) (a b : k)
    (hp : p * p = p) (hmacro : p * σ * p = σ * p) :
    p * (a • (1 : A) + b • σ) * p = (a • (1 : A) + b • σ) * p := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, hp, hmacro]

/-- First-order annihilation removes only the binary coefficient. -/
theorem binary_micro_compression (p σ : A) (a b : k)
    (hp : p * p = p) (hmicro : p * σ * p = 0) :
    p * (a • (1 : A) + b • σ) * p = a • p := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, hp, hmicro, smul_zero, add_zero]

/-- The ordered compression defect follows from the existing Peirce defect
owner and an involution with zero compressed first moment. -/
theorem binary_micro_compression_variance (p σ : A) (a b : k)
    (hp : p * p = p) (hσ : σ * σ = 1) (hmicro : p * σ * p = 0) :
    let L := a • (1 : A) + b • σ
    p * (L * L) * p - (p * L * p) * (p * L * p) = (b * b) • p := by
  dsimp only
  rw [compression_square_defect p _ hp]
  have hpq : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have hqp : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hleft : p * (a • (1 : A) + b • σ) * (1 - p) =
      b • (p * σ * (1 - p)) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, hpq, smul_zero, zero_add]
  have hright : (1 - p) * (a • (1 : A) + b • σ) * p =
      b • ((1 - p) * σ * p) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, hqp, smul_zero, zero_add]
  have htransfer : (p * σ * (1 - p)) * ((1 - p) * σ * p) = p := by
    rw [← compression_square_defect p σ hp, hσ, mul_one, hp, hmicro]
    simp
  rw [hleft, hright, smul_mul_smul_comm, htransfer]

end AlgebraicCompression

section BinaryCharacter

variable {k G : Type u} [Field k] [Group G]
variable (H : Subgroup G) [Fintype H] [Invertible (Fintype.card H : k)]

local notation "ρH" => MonoidHom.comp (rightRegular (k := k) (G := G)) (Subgroup.subtype H)
local notation "P" => Representation.averageMap ρH

/-- An order-two character defines an actual involutive multiplication operator. -/
theorem characterMultiplier_involution (χ : G →* k)
    (hχ : ∀ x : G, χ x * χ x = 1) :
    LinearMap.mulLeft k (χ : G → k) * LinearMap.mulLeft k (χ : G → k) = 1 := by
  ext f x
  change χ x * (χ x * f x) = f x
  rw [← mul_assoc, hχ, one_mul]

/-- The subgroup hypotheses now construct every projector and zero-corner
hypothesis needed by the binary compression identity. -/
theorem subgroup_binary_compression (χ : G →* k) (a b : k)
    (hmicro : ∃ h : H, χ (h : G) ≠ 1) :
    P * (a • (1 : Module.End k (G → k)) + b • LinearMap.mulLeft k (χ : G → k)) * P =
      a • P :=
  binary_micro_compression P _ a b (subgroupAverage_idempotent H)
    (subgroupAverage_character_micro H χ hmicro)

/-- A binary character lost at first order has this exact second-order defect
on the genuine finite-subgroup invariant projection. -/
theorem subgroup_binary_compression_variance (χ : G →* k) (a b : k)
    (hχ : ∀ x : G, χ x * χ x = 1)
    (hmicro : ∃ h : H, χ (h : G) ≠ 1) :
    let L := a • (1 : Module.End k (G → k)) + b • LinearMap.mulLeft k (χ : G → k)
    P * (L * L) * P - (P * L * P) * (P * L * P) = (b * b) • P :=
  binary_micro_compression_variance P _ a b (subgroupAverage_idempotent H)
    (characterMultiplier_involution χ hχ) (subgroupAverage_character_micro H χ hmicro)

/-- Nonzero variance requires and, for this actual nonzero average, is
equivalent to a nonzero binary coefficient. -/
theorem subgroup_binary_variance_ne_zero_iff (χ : G →* k) (a b : k)
    (hχ : ∀ x : G, χ x * χ x = 1)
    (hmicro : ∃ h : H, χ (h : G) ≠ 1) :
    let L := a • (1 : Module.End k (G → k)) + b • LinearMap.mulLeft k (χ : G → k)
    P * (L * L) * P - (P * L * P) * (P * L * P) ≠ 0 ↔ b ≠ 0 := by
  dsimp only
  rw [subgroup_binary_compression_variance H χ a b hχ hmicro]
  simp only [ne_eq, smul_eq_zero, mul_eq_zero, or_self, subgroupAverage_ne_zero H,
    or_false]

end BinaryCharacter

end InfoGeometry.Algebra.SubgroupCompressionVariance
