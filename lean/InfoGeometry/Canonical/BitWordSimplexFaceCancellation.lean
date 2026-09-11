import Mathlib.Data.Fin.SuccPred
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Finite face-cancellation helpers

This small owner isolates the finite `Fin 3` face identities used when
developing the alternating simplex coboundary.  Keeping these identities
independent of the BitWord algebra avoids unfolding a nested generic sum in
the main differential owner.
-/

namespace InfoGeometry.Canonical.BitWordSimplexFaceCancellation

/-! The two orders of deleting two faces are identified by Mathlib's
`succAbove`/`predAbove` interchange theorem.  This is the index equality
used by the pairwise cancellation in the simplicial coboundary square. -/

theorem nested_succAbove_swap {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) =
      i.succAbove (j.succAbove k) := by
  exact Fin.succAbove_succAbove_succAbove_predAbove i j k

theorem nested_succAbove_swap_comp {n : ℕ} {α : Type*}
    (f : Fin (n + 2) → α)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    f ∘ (fun x => (i.succAbove j).succAbove ((j.predAbove i).succAbove x)) =
      f ∘ (fun x => i.succAbove (j.succAbove x)) := by
  congr 1
  funext x
  exact nested_succAbove_swap i j x

theorem face_index_split (p q : ℕ) (i : Fin (p + q + 2)) :
    (∃ j : Fin (p + 1), i.val = j.val) ∨
      (∃ j : Fin (q + 1), i.val = p + 1 + j.val) := by
  by_cases h : i.val ≤ p
  · left
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  · right
    let j : Fin (q + 1) := ⟨i.val - (p + 1), by omega⟩
    refine ⟨j, ?_⟩
    dsimp [j]
    omega

theorem face_index_front_iff (p q : ℕ) (i : Fin (p + q + 2)) :
    (∃ j : Fin (p + 1), i.val = j.val) ↔ i.val ≤ p := by
  constructor
  · rintro ⟨j, h⟩
    omega
  · intro h
    exact ⟨⟨i.val, by omega⟩, rfl⟩

theorem face_index_back_iff (p q : ℕ) (i : Fin (p + q + 2)) :
    (∃ j : Fin (q + 1), i.val = p + 1 + j.val) ↔ p < i.val := by
  constructor
  · rintro ⟨j, h⟩
    omega
  · intro h
    let j : Fin (q + 1) := ⟨i.val - (p + 1), by omega⟩
    exact ⟨j, by dsimp [j]; omega⟩

theorem face_index_split_disjoint (p q : ℕ) (i : Fin (p + q + 2)) :
    ¬ ((∃ j : Fin (p + 1), i.val = j.val) ∧
      (∃ j : Fin (q + 1), i.val = p + 1 + j.val)) := by
  rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
  have hlt : j.val < p + 1 + k.val := by omega
  omega

theorem delete_zero_one :
    (Fin.succAbove (0 : Fin 3) ∘ Fin.succAbove (0 : Fin 2)) =
      (Fin.succAbove (1 : Fin 3) ∘ Fin.succAbove (0 : Fin 2)) := by
  funext i
  fin_cases i
  rfl

theorem delete_zero_two :
    (Fin.succAbove (0 : Fin 3) ∘ Fin.succAbove (1 : Fin 2)) =
      (Fin.succAbove (2 : Fin 3) ∘ Fin.succAbove (0 : Fin 2)) := by
  funext i
  fin_cases i
  rfl

theorem delete_one_two :
    (Fin.succAbove (1 : Fin 3) ∘ Fin.succAbove (1 : Fin 2)) =
      (Fin.succAbove (2 : Fin 3) ∘ Fin.succAbove (1 : Fin 2)) := by
  funext i
  fin_cases i
  rfl

theorem repeated_pair_faces_eq {α : Type*}
    (σ : Fin 2 → α) (hσ : σ 0 = σ 1) :
    σ ∘ Fin.succAbove (0 : Fin 2) =
      σ ∘ Fin.succAbove (1 : Fin 2) := by
  funext i
  fin_cases i
  · simpa using hσ.symm

end InfoGeometry.Canonical.BitWordSimplexFaceCancellation
