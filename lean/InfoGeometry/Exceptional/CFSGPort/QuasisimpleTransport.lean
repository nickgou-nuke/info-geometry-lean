/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local API port of the quasisimple-to-simple quotient transport used by the
external CFSG exceptional Lie-type simplicity proofs. This file does not
establish quasisimplicity for any exceptional Chevalley group.
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Simple

public section

set_option linter.style.haveILetI false

namespace InfoGeometry.Exceptional.CFSGPort.Simplicity

variable {Q : Type*} [Group Q]

/-- CFSG's quasisimplicity contract: perfectness and a nonabelian simple
central quotient. -/
def IsQuasisimple (Q : Type*) [Group Q] : Prop :=
  Group.IsPerfect Q ∧ IsSimpleGroup (Q ⧸ Subgroup.center Q) ∧
    ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a

/-- A perfect group cannot be generated modulo a proper normal subgroup by a
solvable subgroup. This is the quotient argument used in CFSG's Tits
simplicity criterion. -/
theorem eq_top_of_sup_eq_top {Q : Type*} [Group Q] {B M : Subgroup Q}
    [M.Normal] (hperf : Group.IsPerfect Q) (hB : Group.IsSolvable B)
    (h : M ⊔ B = ⊤) : M = ⊤ := by
  haveI := hperf
  haveI := hB
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp B.subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hg : g ∈ M ⊔ B := h ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨m, hm, b, hb, rfl⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).2 hm, one_mul]
  haveI : Group.IsSolvable (Q ⧸ M) := Group.isSolvable_of_surjective hsurj
  rw [eq_top_iff]
  intro g _
  by_contra hg
  haveI : Nontrivial (Q ⧸ M) :=
    ⟨⟨(g : Q ⧸ M), 1, fun h' => hg ((QuotientGroup.eq_one_iff g).1 h')⟩⟩
  exact Group.IsPerfect.not_isSolvable (Q ⧸ M) inferInstance

/-- If every normal subgroup of a perfect group is central or total, its
central quotient is simple. -/
theorem isSimpleGroup_quotient_center_of_forall {Q : Type*} [Group Q] [Nontrivial Q]
    (hperf : Group.IsPerfect Q)
    (h : ∀ M : Subgroup Q, M.Normal → M ≤ Subgroup.center Q ∨ M = ⊤) :
    IsSimpleGroup (Q ⧸ Subgroup.center Q) := by
  haveI := hperf
  obtain ⟨g, hg⟩ : ∃ g, g ∉ Subgroup.center Q := by
    by_contra! h'
    haveI : IsMulCommutative Q :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h' a) b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative Q inferInstance
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) :=
    ⟨⟨(g : Q ⧸ Subgroup.center Q), 1,
      fun h' => hg ((QuotientGroup.eq_one_iff g).1 h')⟩⟩
  refine ⟨fun N hN => ?_⟩
  rcases h _ (hN.comap (QuotientGroup.mk' (Subgroup.center Q))) with hle | htop
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).2 (hle hy)
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have : g ∈ N.comap (QuotientGroup.mk' (Subgroup.center Q)) :=
      htop ▸ Subgroup.mem_top g
    exact this

/-- A perfect group whose normal subgroups are central or total is
quasisimple. -/
theorem isQuasisimple_of_forall {Q : Type*} [Group Q]
    [Nontrivial Q] (hperf : Group.IsPerfect Q)
    (h : ∀ M : Subgroup Q, M.Normal → M ≤ Subgroup.center Q ∨ M = ⊤) :
    IsQuasisimple Q := by
  have hs := isSimpleGroup_quotient_center_of_forall hperf h
  haveI := hperf
  refine ⟨hperf, hs, ?_⟩
  by_contra! hc
  haveI : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hc⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q) inferInstance

/-- A group isomorphic to the central quotient of a quasisimple group is
simple. This is the transport step used by the external exceptional family
theorems; the family-specific quasisimplicity proofs remain separate. -/
theorem isSimpleGroup_of_mulEquiv {G : Type*} [Group G]
    (hQ : IsQuasisimple Q) (e : G ≃* Q ⧸ Subgroup.center Q) : IsSimpleGroup G := by
  letI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  letI : Nontrivial G := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- A centerless quasisimple group is simple. This is the local form of the
external adjoint-group transport used after the exceptional quasisimplicity
proofs. -/
theorem isSimpleGroup_of_quasisimple_centerless
    (hQ : IsQuasisimple Q) (hcenter : Subgroup.center Q = ⊥) :
    IsSimpleGroup Q := by
  exact isSimpleGroup_of_mulEquiv hQ
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm

end InfoGeometry.Exceptional.CFSGPort.Simplicity

end
