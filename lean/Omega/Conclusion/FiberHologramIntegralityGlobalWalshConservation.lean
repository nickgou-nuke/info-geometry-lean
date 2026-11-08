import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

private def conclusion_fiber_hologram_integrality_global_walsh_conservation_flip
    {m : ℕ} (i : Fin m) (ω : Fin m → Bool) : Fin m → Bool :=
  Function.update ω i (!(ω i))

private lemma conclusion_fiber_hologram_integrality_global_walsh_conservation_flip_self
    {m : ℕ} (i : Fin m) (ω : Fin m → Bool) :
    conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i
        (conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω) = ω := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [conclusion_fiber_hologram_integrality_global_walsh_conservation_flip]
  · simp [conclusion_fiber_hologram_integrality_global_walsh_conservation_flip, hji]

private lemma conclusion_fiber_hologram_integrality_global_walsh_conservation_pow_flip
    {m : ℕ} (I : Finset (Fin m)) {i : Fin m} (hi : i ∈ I) (ω : Fin m → Bool) :
    (-1 : ℤ) ^
        ((I.filter fun j =>
          conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω j =
            true).card) =
      -((-1 : ℤ) ^ ((I.filter fun j => ω j = true).card)) := by
  classical
  have hI : I = insert i (I.erase i) := (Finset.insert_erase hi).symm
  have hni : i ∉ I.erase i := fun h => (Finset.mem_erase.mp h).1 rfl
  have hfilter : (I.erase i).filter (fun j => conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω j = true) =
      (I.erase i).filter (fun j => ω j = true) := by
    apply Finset.filter_congr
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [conclusion_fiber_hologram_integrality_global_walsh_conservation_flip, hji]
  by_cases hω : ω i = true
  · have hflip_i : conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω i = false := by
      simp [conclusion_fiber_hologram_integrality_global_walsh_conservation_flip, hω]
    have h1 : (I.filter fun j => conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω j = true) =
        (I.erase i).filter (fun j => ω j = true) := by
      nth_rw 1 [hI]
      rw [Finset.filter_insert]
      simp [hflip_i, hfilter]
    have h2 : (I.filter fun j => ω j = true) =
        insert i ((I.erase i).filter (fun j => ω j = true)) := by
      nth_rw 1 [hI]
      rw [Finset.filter_insert]
      simp [hω]
    have hnotmem : i ∉ (I.erase i).filter (fun j => ω j = true) := by
      intro hmem
      exact hni (Finset.mem_of_mem_filter i hmem)
    rw [h1, h2, Finset.card_insert_of_notMem hnotmem, pow_succ]
    ring
  · have hnot : ω i = false := by
      cases h : ω i
      · rfl
      · contradiction
    have hflip_i : conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω i = true := by
      simp [conclusion_fiber_hologram_integrality_global_walsh_conservation_flip, hnot]
    have h1 : (I.filter fun j => conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω j = true) =
        insert i ((I.erase i).filter (fun j => ω j = true)) := by
      nth_rw 1 [hI]
      rw [Finset.filter_insert]
      simp [hflip_i, hfilter]
    have h2 : (I.filter fun j => ω j = true) =
        (I.erase i).filter (fun j => ω j = true) := by
      nth_rw 1 [hI]
      rw [Finset.filter_insert]
      simp [hnot]
    have hnotmem : i ∉ (I.erase i).filter (fun j => ω j = true) := by
      intro hmem
      exact hni (Finset.mem_of_mem_filter i hmem)
    rw [h1, h2, Finset.card_insert_of_notMem hnotmem, pow_succ]
    ring

private lemma conclusion_fiber_hologram_integrality_global_walsh_conservation_sum_eq_zero
    {m : ℕ} (I : Finset (Fin m)) (hI : I ≠ ∅) :
    (∑ ω : Fin m → Bool, (-1 : ℤ) ^ ((I.filter fun i => ω i = true).card)) = 0 := by
  classical
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hI
  refine Finset.sum_involution
    (s := (Finset.univ : Finset (Fin m → Bool)))
    (f := fun ω => (-1 : ℤ) ^ ((I.filter fun i => ω i = true).card))
    (g := fun ω _ =>
      conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω) ?_ ?_ ?_ ?_
  · intro ω _
    change
      (-1 : ℤ) ^ ((I.filter fun i => ω i = true).card) +
          (-1 : ℤ) ^
            ((I.filter fun j =>
              conclusion_fiber_hologram_integrality_global_walsh_conservation_flip i ω j =
                true).card) =
        0
    rw [conclusion_fiber_hologram_integrality_global_walsh_conservation_pow_flip I hi]
    abel
  · intro ω _ _hω hfix
    have hcoord := congr_fun hfix i
    simp [conclusion_fiber_hologram_integrality_global_walsh_conservation_flip] at hcoord
  · intro ω _
    simp
  · intro ω _
    exact conclusion_fiber_hologram_integrality_global_walsh_conservation_flip_self i ω

private lemma conclusion_fiber_hologram_integrality_global_walsh_conservation_sum_fibers
    {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (Fold : (Fin m → Bool) → X) (I : Finset (Fin m)) :
    (∑ x : X, ∑ ω : Fin m → Bool,
      if Fold ω = x then ((-1 : ℤ) ^ ((I.filter fun i => ω i = true).card)) else 0) =
      ∑ ω : Fin m → Bool, (-1 : ℤ) ^ ((I.filter fun i => ω i = true).card) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.sum_eq_single (Fold ω)]
  · simp
  · intro x _hx hx
    exact if_neg fun h => hx h.symm
  · intro hx
    exact (hx (by simp)).elim

/-- Paper label: `prop:conclusion-fiber-hologram-integrality-global-walsh-conservation`. Summing
the signed Walsh counts over all fibers gives the cube cardinality for the trivial character and
zero for every nontrivial character. -/
theorem paper_conclusion_fiber_hologram_integrality_global_walsh_conservation
    {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (Fold : (Fin m → Bool) → X) (I : Finset (Fin m)) :
    (∑ x : X, ∑ ω : Fin m → Bool,
      if Fold ω = x then ((-1 : ℤ) ^ ((I.filter fun i => ω i = true).card)) else 0) =
      if I = ∅ then (2 : ℤ) ^ m else 0 := by
  classical
  rw [conclusion_fiber_hologram_integrality_global_walsh_conservation_sum_fibers Fold I]
  by_cases hI : I = ∅
  · subst hI
    simp
  · rw [if_neg hI]
    exact conclusion_fiber_hologram_integrality_global_walsh_conservation_sum_eq_zero I hI

end Omega.Conclusion
