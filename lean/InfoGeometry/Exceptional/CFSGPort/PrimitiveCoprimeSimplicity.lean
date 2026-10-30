/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import Mathlib
public import InfoGeometry.Exceptional.CFSGPort.QuasisimpleTransport

/-!
# Primitive action criterion for simplicity

This ports the reusable primitive-action criterion used by the external CFSG
sporadic proofs. A faithful preprimitive action turns every nontrivial normal
subgroup into a transitive subgroup; the point stabilizer then bounds the
quotient order, and coprime generator-order conditions force the quotient to
be trivial.
-/

public section

namespace InfoGeometry.Exceptional.CFSGPort.GroupActions

/-- A nontrivial normal subgroup in a faithful preprimitive action is
transitive. -/
theorem isPretransitive_of_normal_ne_bot
    {G Ω : Type*} [Group G] [MulAction G Ω] [Nonempty Ω]
    [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    MulAction.IsPretransitive N Ω := by
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  have hnotfixed : MulAction.fixedPoints N Ω ≠ Set.univ := by
    intro hfixed
    apply not_subsingleton N
    constructor
    intro a b
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
    intro x
    have hx : x ∈ MulAction.fixedPoints N Ω := hfixed.symm ▸ Set.mem_univ x
    exact (hx a).trans (hx b).symm
  exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hnotfixed

/-- A perfect group with a faithful preprimitive action and solvable point
stabilizer is simple. This ports the generic primitive-action simplicity
criterion used by the external CFSG sporadic-group proofs. -/
theorem isSimpleGroup_of_isPreprimitive_of_isSolvable_stabilizer
    {G Ω : Type*} [Group G] [Nontrivial G] [MulAction G Ω]
    [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (hperf : Group.IsPerfect G) (ω : Ω)
    (hsolv : Group.IsSolvable (MulAction.stabilizer G ω)) : IsSimpleGroup G := by
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, ?_⟩
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  let _ : N.Normal := hN
  have hfix : MulAction.fixedPoints N Ω ≠ Set.univ := by
    intro h
    apply hNbot
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine eq_of_smul_eq_smul (α := Ω) fun y => ?_
    have hy : y ∈ MulAction.fixedPoints N Ω := h ▸ Set.mem_univ y
    rw [one_smul]
    exact hy ⟨g, hg⟩
  letI : MulAction.IsPretransitive N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
  have hsup : N ⊔ MulAction.stabilizer G ω = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N ω (g • ω)
    have hstab : (n : G)⁻¹ * g ∈ MulAction.stabilizer G ω := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hn, Subgroup.smul_def,
        inv_smul_smul]
    have he : g = (n : G) * ((n : G)⁻¹ * g) := by group
    rw [he]
    exact mul_mem (Subgroup.mem_sup_left n.2)
      (Subgroup.mem_sup_right hstab)
  exact InfoGeometry.Exceptional.CFSGPort.Simplicity.eq_top_of_sup_eq_top
    hperf hsolv hsup

/-- Factor an element as a transitive normal-subgroup element followed by a
point stabilizer element. -/
theorem exists_mul_stabilizer_eq
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (N : Subgroup G) [MulAction.IsPretransitive N Ω] (ω : Ω) (g : G) :
    ∃ (n : N) (h : MulAction.stabilizer G ω), (n : G) * (h : G) = g := by
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N ω (g • ω)
  refine ⟨n, ⟨(n : G)⁻¹ * g, ?_⟩, by simp⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul]
  have hn' : (n : G) • ω = g • ω := hn
  rw [← hn', inv_smul_smul]

/-- The point stabilizer maps onto the quotient by a transitive normal
subgroup. -/
theorem stabilizer_quotient_surjective
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N Ω] (ω : Ω) :
    Function.Surjective
      ((QuotientGroup.mk' N).comp (MulAction.stabilizer G ω).subtype) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨n, h, hnh⟩ := exists_mul_stabilizer_eq N ω g
  refine ⟨h, ?_⟩
  change (h : G ⧸ N) = (g : G ⧸ N)
  rw [← hnh, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr n.property,
    one_mul]

/-- If a normal subgroup acts transitively, the quotient group's cardinality
divides the cardinality of a point stabilizer. -/
theorem quotient_card_dvd_stabilizer_card
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N Ω] (ω : Ω) :
    Nat.card (G ⧸ N) ∣ Nat.card (MulAction.stabilizer G ω) :=
  Subgroup.card_dvd_of_surjective
    ((QuotientGroup.mk' N).comp (MulAction.stabilizer G ω).subtype)
    (stabilizer_quotient_surjective N ω)

/-- Simplicity criterion from a faithful preprimitive action and two
coprimality conditions on generators. -/
theorem isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    {G Ω : Type*} [Group G] [Finite G] [Finite Ω]
    [MulAction G Ω] [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (hΩ : 2 ≤ Nat.card Ω) (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (ω : Ω)
    (hab : (orderOf a).Coprime (orderOf b))
    (hst : (orderOf (a * b)).Coprime (Nat.card (MulAction.stabilizer G ω))) :
    IsSimpleGroup G := by
  classical
  let _ : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (Nat.lt_of_succ_le hΩ)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  have hg_ne : g ≠ 1 := by
    intro h
    apply hxy
    simpa [h] using hg
  let _ : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, ?_⟩
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  let _ : N.Normal := hN
  let _ : MulAction.IsPretransitive N Ω := isPretransitive_of_normal_ne_bot N hNbot
  let φ : G →* G ⧸ N := QuotientGroup.mk' N
  have hcard : Nat.card (G ⧸ N) ∣ Nat.card (MulAction.stabilizer G ω) :=
    quotient_card_dvd_stabilizer_card N ω
  have hprod : φ (a * b) = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hst (orderOf_map_dvd φ (a * b))
      ((orderOf_dvd_natCard (φ (a * b))).trans hcard)
  have hinv : φ a = (φ b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa using hprod
  have ha : φ a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hab (orderOf_map_dvd φ a)
    rw [hinv, orderOf_inv]
    exact orderOf_map_dvd φ b
  have hb : φ b = 1 := by
    simpa [map_mul, ha] using hprod
  have haN : a ∈ N := (QuotientGroup.eq_one_iff a).mp ha
  have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).mp hb
  apply top_le_iff.mp
  rw [← hgen]
  apply (Subgroup.closure_le N).mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact haN
  · exact hbN

end InfoGeometry.Exceptional.CFSGPort.GroupActions
