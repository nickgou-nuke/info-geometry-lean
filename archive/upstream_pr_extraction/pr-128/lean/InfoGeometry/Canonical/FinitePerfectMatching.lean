import Mathlib

namespace InfoGeometry.Canonical.FinitePerfectMatching

noncomputable section

structure PerfectMatching (m : ℕ) where
  partner : Fin (2 * m) → Fin (2 * m)
  involutive : Function.Involutive partner
  fixed_free : ∀ i, partner i ≠ i

namespace PerfectMatching

variable {m : ℕ} (M : PerfectMatching m)

def leftEndpoints : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun i => i < M.partner i)

def rightEndpoints : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun i => M.partner i < i)

theorem partner_ne (i : Fin (2 * m)) : i ≠ M.partner i :=
  Ne.symm (M.fixed_free i)

theorem left_or_right (i : Fin (2 * m)) :
    i ∈ M.leftEndpoints ∨ i ∈ M.rightEndpoints := by
  unfold leftEndpoints rightEndpoints
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_or_gt_of_ne (M.partner_ne i)

theorem left_union_right :
    M.leftEndpoints ∪ M.rightEndpoints = Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_univ]
  exact iff_of_true (M.left_or_right i) trivial

theorem left_inter_right :
    M.leftEndpoints ∩ M.rightEndpoints = ∅ := by
  apply Finset.subset_empty.mp
  intro i hi
  exact False.elim ((not_lt_of_ge
      (le_of_lt (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2))
    (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2)

theorem left_card_eq_right_card :
    M.leftEndpoints.card = M.rightEndpoints.card := by
  apply Finset.card_bij (fun i _ => M.partner i)
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    unfold rightEndpoints
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [M.involutive i] using hi'
  · intro i hi j hj h
    have := congrArg M.partner h
    simpa [M.involutive i, M.involutive j] using this
  · intro j hj
    unfold rightEndpoints at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨M.partner j, ?_, M.involutive j⟩
    unfold leftEndpoints
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [M.involutive j] using hj

theorem left_card_add_right_card :
    M.leftEndpoints.card + M.rightEndpoints.card = 2 * m := by
  rw [← Finset.card_union_of_disjoint]
  · rw [M.left_union_right]
    simp
  · exact Finset.disjoint_left.mpr (by
      intro i hil hir
      exact (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp hir).2))
        (Finset.mem_filter.mp hil).2)

theorem leftEndpoints_card : M.leftEndpoints.card = m := by
  have h := M.left_card_add_right_card
  have heq := M.left_card_eq_right_card
  omega

end PerfectMatching
end
end InfoGeometry.Canonical.FinitePerfectMatching
