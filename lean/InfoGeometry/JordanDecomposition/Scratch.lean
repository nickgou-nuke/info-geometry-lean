import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open FiniteDimensional
open Submodule

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def NilpotentIndexScratch (N : Module.End K V) (k : ℕ) : Prop :=
  (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

lemma linearIndependent_cyclic_step (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndexScratch N k) (x : V) (hx : (N ^ (k - 1)) x ≠ 0)
    (l : Fin k → K) (hl : (show V from ∑ i : Fin k, l i • (N ^ (i : ℕ)) x) = 0)
    (d : ℕ) (hd : d < k) (h_ind : ∀ i : Fin k, (i : ℕ) < d → l i = 0) :
    l ⟨d, hd⟩ = 0 := by
  have h_app : (N ^ (k - 1 - d)) ((show V from ∑ i : Fin k, l i • (N ^ (i : ℕ)) x)) = 0 := by
    rw [hl, map_zero]
  have h_sum : (N ^ (k - 1 - d)) (∑ i : Fin k, l i • (N ^ (i : ℕ)) x) =
      ∑ i : Fin k, l i • (N ^ (k - 1 - d) * N ^ (i : ℕ)) x := by
    rw [map_sum]
    simp only [map_smul]
    rfl
  have h_term : ∀ i : Fin k, i ≠ ⟨d, hd⟩ → l i • (N ^ (k - 1 - d) * N ^ (i : ℕ)) x = 0 := by
    intro i hi
    have h_cases : (i : ℕ) < d ∨ (i : ℕ) > d := by
      rcases lt_trichotomy (i : ℕ) d with h | h | h
      · exact Or.inl h
      · exfalso
        apply hi
        ext
        exact h
      · exact Or.inr h
    rcases h_cases with h_lt | h_gt
    · have hl_zero : l i = 0 := h_ind i h_lt
      rw [hl_zero, zero_smul]
    · have h_pow_sum : k - 1 - d + (i : ℕ) = k + ((i : ℕ) - d - 1) := by
        omega
      have h_op : N ^ (k - 1 - d) * N ^ (i : ℕ) = 0 := by
        rw [← pow_add, h_pow_sum, pow_add, hN.1, zero_mul]
      rw [h_op]
      simp
  have h_single : (∑ i : Fin k, l i • (N ^ (k - 1 - d) * N ^ (i : ℕ)) x) =
      l ⟨d, hd⟩ • (N ^ (k - 1 - d) * N ^ d) x := by
    have h_eq : (fun i : Fin k => l i • (N ^ (k - 1 - d) * N ^ (i : ℕ)) x) ⟨d, hd⟩ =
        l ⟨d, hd⟩ • (N ^ (k - 1 - d) * N ^ d) x := by
      rfl
    rw [← h_eq]
    apply Finset.sum_eq_single (⟨d, hd⟩ : Fin k)
    · intro b _ hb
      exact h_term b hb
    · intro h_not_mem
      exfalso
      apply h_not_mem
      simp
  have h_pow_eq : N ^ (k - 1 - d) * N ^ d = N ^ (k - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h_zero : l ⟨d, hd⟩ • (N ^ (k - 1)) x = 0 := by
    rw [← h_pow_eq]
    rw [← h_single]
    rw [← h_sum]
    exact h_app
  rcases smul_eq_zero.mp h_zero with hl | hx_zero
  · exact hl
  · exfalso
    exact hx hx_zero

lemma linearIndependent_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndexScratch N k) (x : V) (hx : (N ^ (k - 1)) x ≠ 0) :
    LinearIndependent K (fun (i : Fin k) => (N ^ (i : ℕ)) x) := by
  apply Fintype.linearIndependent_iff.mpr
  intro l hl i
  have h_all : ∀ (d : ℕ) (hd : d ≤ k) (j : Fin k) (hj : (j : ℕ) < d), l j = 0 := by
    intro d
    induction d with
    | zero =>
      intro _ j hj
      exfalso
      omega
    | succ d ih =>
      intro hd j hj
      have h_cases : (j : ℕ) < d ∨ (j : ℕ) = d := by
        omega
      rcases h_cases with h_lt | h_eq
      · exact ih (by omega) j h_lt
      · have hd_lt : d < k := by omega
        have h_ind_step : ∀ i : Fin k, (i : ℕ) < d → l i = 0 := by
          intro i hi
          exact ih (by omega) i hi
        have hl_d : l ⟨d, hd_lt⟩ = 0 := by
          exact linearIndependent_cyclic_step N k hN x hx l hl d hd_lt h_ind_step
        have hj_eq : j = ⟨d, hd_lt⟩ := by
          ext
          exact h_eq
        rw [hj_eq]
        exact hl_d
  exact h_all k (le_refl k) i i.isLt
