/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Toggle coordinate `i` in a path-independent set when the result remains
path-independent; an occupied neighboring vertex blocks insertion. -/
def pathToggleFinset (ell : ℕ) (i : Fin ell) (S : Finset (Fin ell)) :
    Finset (Fin ell) :=
  if hi : i ∈ S then S.erase i
  else if hfree : ∀ j ∈ S,
      j.val + 1 ≠ i.val ∧ i.val + 1 ≠ j.val then insert i S
  else S

theorem pathToggleFinset_independent (ell : ℕ) (i : Fin ell)
    (S : Finset (Fin ell)) (hS : IsPathIndependent ell S) :
    IsPathIndependent ell (pathToggleFinset ell i S) := by
  by_cases hi : i ∈ S
  · simp only [pathToggleFinset, dif_pos hi]
    intro a ha b hb hab
    exact hS a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
  · by_cases hfree : ∀ j ∈ S,
        j.val + 1 ≠ i.val ∧ i.val + 1 ≠ j.val
    · simp only [pathToggleFinset, dif_neg hi, dif_pos hfree]
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hai | ha
      · subst a
        rcases Finset.mem_insert.mp hb with hbi | hb
        · subst b
          exact (Nat.ne_of_gt (Nat.lt_succ_self i.val)) hab
        · exact (hfree b hb).2 hab
      · rcases Finset.mem_insert.mp hb with hbi | hb
        · subst b
          exact (hfree a ha).1 hab
        · exact hS a ha b hb hab
    · simpa [pathToggleFinset, hi, hfree] using hS

/-- The local toggle as an actual permutation operator on the Fibonacci
configuration carrier. -/
def pathToggleState (ell : ℕ) (i : Fin ell) (x : PathIndSets ell) :
    PathIndSets ell :=
  ⟨pathToggleFinset ell i x.1,
    pathToggleFinset_independent ell i x.1 x.2⟩

theorem pathToggleState_involutive (ell : ℕ) (i : Fin ell) :
    Function.Involutive (pathToggleState ell i) := by
  intro x
  apply Subtype.ext
  change pathToggleFinset ell i (pathToggleFinset ell i x.1) = x.1
  by_cases hi : i ∈ x.1
  · have hfree : ∀ j ∈ x.1.erase i,
        j.val + 1 ≠ i.val ∧ i.val + 1 ≠ j.val := by
      intro j hj
      have hjS := (Finset.mem_erase.mp hj).2
      have hji : ¬ (j.val + 1 = i.val) := x.2 j hjS i hi
      have hij : ¬ (i.val + 1 = j.val) := x.2 i hi j hjS
      exact ⟨hji, hij⟩
    have hnot : i ∉ x.1.erase i := by simp
    have hinner : pathToggleFinset ell i x.1 = x.1.erase i := by
      simp [pathToggleFinset, hi]
    rw [hinner]
    rw [pathToggleFinset, dif_neg hnot, dif_pos hfree]
    exact Finset.insert_erase hi
  · by_cases hfree : ∀ j ∈ x.1,
        j.val + 1 ≠ i.val ∧ i.val + 1 ≠ j.val
    · have hinner : pathToggleFinset ell i x.1 = insert i x.1 := by
        rw [pathToggleFinset, dif_neg hi, dif_pos hfree]
      rw [hinner]
      rw [pathToggleFinset, dif_pos (Finset.mem_insert_self i x.1)]
      simp [Finset.erase_insert, hi]
    · have hinner : pathToggleFinset ell i x.1 = x.1 := by
        rw [pathToggleFinset, dif_neg hi, dif_neg hfree]
      rw [hinner]
      rw [pathToggleFinset, dif_neg hi, dif_neg hfree]

/-- The path-toggle generator, represented as an element of the permutation
group of path-independent states. -/
def pathToggleGenerator (ell : ℕ) (i : Fin ell) :
    Equiv.Perm (PathIndSets ell) :=
  Function.Involutive.toPerm (pathToggleState ell i)
    (pathToggleState_involutive ell i)

@[simp] theorem pathToggleGenerator_apply (ell : ℕ) (i : Fin ell)
    (x : PathIndSets ell) :
    pathToggleGenerator ell i x = pathToggleState ell i x := rfl

theorem pathToggleGenerator_involutive (ell : ℕ) (i : Fin ell) :
    Function.Involutive (pathToggleGenerator ell i) := by
  intro x
  exact pathToggleState_involutive ell i x

def pathToggleEmptyState (ell : ℕ) : PathIndSets ell :=
  ⟨∅, by simp [IsPathIndependent]⟩

def pathToggleSingletonState (ell : ℕ) (i : Fin ell) : PathIndSets ell :=
  ⟨{i}, by
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact (Nat.ne_of_gt (Nat.lt_succ_self i.val)) hab⟩

theorem pathToggleState_empty (ell : ℕ) (i : Fin ell) :
    pathToggleState ell i (pathToggleEmptyState ell) =
      pathToggleSingletonState ell i := by
  apply Subtype.ext
  change pathToggleFinset ell i ∅ = {i}
  simp [pathToggleFinset]

theorem pathToggleState_singleton_blocked (ell : ℕ) (i j : Fin ell)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    pathToggleState ell i (pathToggleSingletonState ell j) =
      pathToggleSingletonState ell j := by
  apply Subtype.ext
  change pathToggleFinset ell i {j} = {j}
  have hne : i ≠ j := by
    intro h
    subst j
    rcases hij with h | h
    · exact (Nat.ne_of_gt (Nat.lt_succ_self i.val)) h
    · exact (Nat.ne_of_gt (Nat.lt_succ_self i.val)) h
  rcases hij with h | h
  · simp [pathToggleFinset, hne, h]
  · simp [pathToggleFinset, hne, h]

/-- Consecutive path toggles are genuinely noncommuting operators: their two
orders send the empty independent set to different singleton states. -/
theorem pathToggleGenerator_adjacent_noncommute (ell : ℕ) (i j : Fin ell)
    (hij : i.val + 1 = j.val) :
    pathToggleGenerator ell i * pathToggleGenerator ell j ≠
      pathToggleGenerator ell j * pathToggleGenerator ell i := by
  intro h
  have hLeft :
      (pathToggleGenerator ell i * pathToggleGenerator ell j)
          (pathToggleEmptyState ell) = pathToggleSingletonState ell j := by
    rw [Equiv.Perm.mul_apply, pathToggleGenerator_apply, pathToggleGenerator_apply,
      pathToggleState_empty, pathToggleState_singleton_blocked ell i j (Or.inl hij)]
  have hRight :
      (pathToggleGenerator ell j * pathToggleGenerator ell i)
          (pathToggleEmptyState ell) = pathToggleSingletonState ell i := by
    rw [Equiv.Perm.mul_apply, pathToggleGenerator_apply, pathToggleGenerator_apply,
      pathToggleState_empty, pathToggleState_singleton_blocked ell j i (Or.inr hij)]
  have hEval := congrArg (fun σ : Equiv.Perm (PathIndSets ell) =>
    σ (pathToggleEmptyState ell)) h
  rw [hLeft, hRight] at hEval
  have hval := congrArg Subtype.val hEval
  have hji : j = i := Finset.singleton_inj.mp hval
  have hne : i ≠ j := by
    intro h'
    subst j
    exact (Nat.ne_of_gt (Nat.lt_succ_self i.val)) hij
  exact hne hji.symm

/-- The actual operator group generated by the path-toggle permutations. -/
def pathToggleOperatorClosure (ell : ℕ) :
    Subgroup (Equiv.Perm (PathIndSets ell)) :=
  Subgroup.closure (Set.range (pathToggleGenerator ell))

theorem pathToggleGenerator_mem_closure (ell : ℕ) (i : Fin ell) :
    pathToggleGenerator ell i ∈ pathToggleOperatorClosure ell :=
  Subgroup.subset_closure ⟨i, rfl⟩

end Omega.POM
