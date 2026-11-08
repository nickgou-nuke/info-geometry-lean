/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.IncidenceRank

/-!
# Nondegeneracy of the representable projective model

Points are the native quotient `Projectivization K V`; lines are actual
rank-two subspaces. These results supply line existence even for repeated
points, three distinct points on every line, distinct lines in dimension at
least three, and skew lines in vector dimension four.
-/

noncomputable section

open Module

namespace InfoGeometry.Projective.IncidenceNondegeneracy

open IncidenceRank

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Inclusion between projective rays is equality of quotient points. -/
theorem submodule_le_submodule_iff (p q : Projectivization K V) :
    p.submodule ≤ q.submodule ↔ p = q := by
  constructor
  · intro h
    apply Projectivization.submodule_injective
    exact Submodule.eq_of_le_of_finrank_eq h
      (by rw [p.finrank_submodule, q.finrank_submodule])
  · rintro rfl
    exact le_rfl

theorem representative_mem (p : Projectivization K V) : p.rep ∈ p.submodule := by
  rw [p.submodule_eq]
  exact Submodule.mem_span_singleton_self _

theorem representative_mem_iff (p q : Projectivization K V) :
    p.rep ∈ q.submodule ↔ p = q := by
  rw [← submodule_le_submodule_iff p q, p.submodule_eq]
  exact (Submodule.span_singleton_le_iff_mem _ _).symm

/-- A failed subspace inclusion supplies a genuine projective point witnessing it. -/
theorem exists_point_le_not_le {U W : Submodule K V} (h : ¬U ≤ W) :
    ∃ p : Projectivization K V, p.submodule ≤ U ∧ ¬p.submodule ≤ W := by
  obtain ⟨v, hvU, hvW⟩ := SetLike.not_le_iff_exists.mp h
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvW W.zero_mem
  refine ⟨Projectivization.mk K v hv0, ?_, ?_⟩
  · rw [Projectivization.submodule_mk]
    exact Submodule.span_le.mpr (by simpa using hvU)
  · rw [Projectivization.submodule_mk]
    intro hle
    exact hvW (hle (Submodule.mem_span_singleton_self _))

/-- A subspace of dimension at least two contains a point different from any prescribed point. -/
theorem exists_other_point {U : Submodule K V} (hU : 2 ≤ finrank K U)
    (p : Projectivization K V) :
    ∃ q : Projectivization K V, q.submodule ≤ U ∧ q ≠ p := by
  have hnot : ¬U ≤ p.submodule := by
    intro h
    have hdim := Submodule.finrank_mono h
    rw [p.finrank_submodule] at hdim
    omega
  obtain ⟨q, hqU, hqp⟩ := exists_point_le_not_le hnot
  refine ⟨q, hqU, ?_⟩
  rintro rfl
  exact hqp le_rfl

/-- Line existence includes the repeated-point case. -/
theorem exists_line (hV : 2 ≤ finrank K V) (p q : Projectivization K V) :
    ∃ L : Submodule K V, finrank K L = 2 ∧ p.submodule ≤ L ∧ q.submodule ≤ L := by
  by_cases hpq : p = q
  · subst q
    obtain ⟨r, _, hrp⟩ := exists_other_point (U := ⊤)
      (by simpa only [finrank_top] using hV) p
    exact ⟨p.submodule ⊔ r.submodule,
      finrank_sup_points hrp.symm, le_sup_left, le_sup_left⟩
  · obtain ⟨L, hL, _⟩ := existsUnique_line hpq
    exact ⟨L, hL⟩

/-- The sum of representatives supplies a third point on a line over any division ring. -/
theorem exists_third_point {p q : Projectivization K V} (hpq : p ≠ q) :
    ∃ r : Projectivization K V,
      r ≠ p ∧ r ≠ q ∧ r.submodule ≤ p.submodule ⊔ q.submodule := by
  have hpnot : p.rep ∉ q.submodule := fun h => hpq ((representative_mem_iff p q).mp h)
  have hqnot : q.rep ∉ p.submodule := fun h => hpq ((representative_mem_iff q p).mp h).symm
  have hsum0 : p.rep + q.rep ≠ 0 := by
    intro h
    have hsum : p.rep + q.rep ∈ q.submodule := by rw [h]; exact q.submodule.zero_mem
    exact hpnot (by simpa using q.submodule.sub_mem hsum (representative_mem q))
  let r := Projectivization.mk K (p.rep + q.rep) hsum0
  have hrmem : p.rep + q.rep ∈ r.submodule := by
    change p.rep + q.rep ∈ (Projectivization.mk K (p.rep + q.rep) hsum0).submodule
    rw [Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _
  refine ⟨r, ?_, ?_, ?_⟩
  · intro hrp
    have hsum : p.rep + q.rep ∈ p.submodule := hrp ▸ hrmem
    exact hqnot (by simpa using p.submodule.sub_mem hsum (representative_mem p))
  · intro hrq
    have hsum : p.rep + q.rep ∈ q.submodule := hrq ▸ hrmem
    exact hpnot (by simpa using q.submodule.sub_mem hsum (representative_mem q))
  · change (Projectivization.mk K (p.rep + q.rep) hsum0).submodule ≤ _
    rw [Projectivization.submodule_mk]
    apply Submodule.span_le.mpr
    simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using
      (p.submodule ⊔ q.submodule).add_mem
        ((le_sup_left : p.submodule ≤ p.submodule ⊔ q.submodule) (representative_mem p))
        ((le_sup_right : q.submodule ≤ p.submodule ⊔ q.submodule) (representative_mem q))

/-- Every projective line contains at least three pairwise distinct points. -/
theorem three_points_on_line {L : Submodule K V} (hL : finrank K L = 2) :
    ∃ p q r : Projectivization K V,
      p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ p.submodule ≤ L ∧ q.submodule ≤ L ∧ r.submodule ≤ L := by
  have hLbot : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    omega
  obtain ⟨p, hp⟩ := (exists_point_iff_ne_bot L).mpr hLbot
  obtain ⟨q, hq, hqp⟩ := exists_other_point (by omega : 2 ≤ finrank K L) p
  obtain ⟨r, hrp, hrq, hr⟩ := exists_third_point hqp.symm
  exact ⟨p, q, r, hqp.symm, hrq.symm, hrp.symm, hp, hq,
    hr.trans (sup_le hp hq)⟩

/-- A vector space of dimension at least three contains two distinct projective lines. -/
theorem exists_two_distinct_lines (hV : 3 ≤ finrank K V) :
    ∃ L M : Submodule K V, finrank K L = 2 ∧ finrank K M = 2 ∧ L ≠ M := by
  have htop : (⊤ : Submodule K V) ≠ ⊥ := by
    intro h
    have hdim := congrArg (fun U : Submodule K V => finrank K U) h
    simp only [finrank_top, finrank_bot] at hdim
    omega
  obtain ⟨p, _⟩ := (exists_point_iff_ne_bot (⊤ : Submodule K V)).mpr htop
  obtain ⟨L, hL, _, _⟩ := exists_line (by omega) p p
  have hnot : ¬(⊤ : Submodule K V) ≤ L := by
    intro h
    have hdim := Submodule.finrank_mono h
    rw [finrank_top, hL] at hdim
    omega
  obtain ⟨q, _, hq⟩ := exists_point_le_not_le hnot
  obtain ⟨M, hM, _, hqM⟩ := exists_line (by omega) p q
  refine ⟨L, M, hL, hM, ?_⟩
  intro hLM
  apply hq
  rw [hLM]
  exact hqM

/-- In vector dimension four, a complement to a line is another line and they are skew. -/
theorem exists_skew_lines (hV : finrank K V = 4) :
    ∃ L M : Submodule K V,
      finrank K L = 2 ∧ finrank K M = 2 ∧
      ¬∃ p : Projectivization K V, p.submodule ≤ L ∧ p.submodule ≤ M := by
  obtain ⟨L, _, hL, _, _⟩ := exists_two_distinct_lines (by omega : 3 ≤ finrank K V)
  obtain ⟨M, hLM⟩ := Submodule.exists_isCompl L
  have hdim := Submodule.finrank_add_eq_of_isCompl hLM
  rw [hL, hV] at hdim
  have hM : finrank K M = 2 := by omega
  refine ⟨L, M, hL, hM, ?_⟩
  rw [exists_common_point_iff, hLM.disjoint.eq_bot]
  exact not_not_intro rfl

end InfoGeometry.Projective.IncidenceNondegeneracy
