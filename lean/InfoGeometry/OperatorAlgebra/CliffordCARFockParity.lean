/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cl(n,n) Fock Parity — general n occupation counting

For arbitrary n, the occupation state space `Fin n → Bool` has size 2^n.
The even and odd sectors each have 2^(n-1) states, so the finite Witten
index Tr((-1)^F) = 2^(n-1) - 2^(n-1) = 0.

## What is proved
- n=0: 1 state (empty vacuum), which is even. Witten index = 1 - 0 = 1.
  (A single-mode vacuum cannot support fermionic parity cancellation.)
- n=4: 16 states, 8 even + 8 odd. Witten index = 8 - 8 = 0.
  (The physical Cl(4,4) case.)

The general combinatorial identity is proved below by an explicit involution
that toggles the first mode and exchanges the even and odd sectors.
-/

open Finset

namespace InfoGeometry.OperatorAlgebra.CliffordCARFockParity

/-- Occupation label for n modes. -/
abbrev Occupation (n : ℕ) := Fin n → Bool

/-- Number of occupied modes (fermion number operator eigenvalue). -/
def fermionNumber {n : ℕ} (w : Occupation n) : ℕ :=
  ∑ i : Fin n, if w i then 1 else 0

/-! ### General parity balance -/

/-- The first mode of a nonempty occupation space. -/
def firstMode {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

/-- Toggle the occupation of the first mode. -/
def toggleFirst {n : ℕ} (hn : 0 < n) (w : Occupation n) : Occupation n :=
  fun i => if i = firstMode hn then !w i else w i

theorem toggleFirst_involutive {n : ℕ} (hn : 0 < n) :
    Function.Involutive (toggleFirst hn) := by
  intro w
  funext i
  by_cases h : i = firstMode hn <;> simp [toggleFirst, h]

lemma fermionNumber_toggleFirst_eq_add_or_sub {n : ℕ} (hn : 0 < n) (w : Occupation n) :
    fermionNumber (toggleFirst hn w) =
      if w (firstMode hn) then fermionNumber w - 1 else fermionNumber w + 1 := by
  by_cases h0 : w (firstMode hn) = true
  · have hle : 1 ≤ fermionNumber w := by
      unfold fermionNumber
      rw [← Finset.card_filter]
      apply Finset.one_le_card.mpr
      exact ⟨firstMode hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
    have hnum : fermionNumber (toggleFirst hn w) = fermionNumber w - 1 := by
      simp [fermionNumber, toggleFirst]
      have hset :
          (Finset.univ.filter fun x : Fin n =>
              if x = firstMode hn then w x = false else w x = true) =
            (Finset.univ.filter fun x : Fin n => w x = true).erase (firstMode hn) := by
        ext x
        by_cases hx : x = firstMode hn
        · subst hx
          simpa [Finset.mem_filter, Finset.mem_erase] using h0
        · simp [hx, Finset.mem_filter, Finset.mem_erase]
      rw [hset]
      have hmem : firstMode hn ∈ Finset.univ.filter fun x : Fin n => w x = true := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
      have h := Finset.card_erase_add_one
        (s := Finset.univ.filter fun x : Fin n => w x = true) hmem
      omega
    simpa [h0] using hnum
  · have h0' : w (firstMode hn) = false := Bool.eq_false_of_not_eq_true h0
    have hnum : fermionNumber (toggleFirst hn w) = fermionNumber w + 1 := by
      simp [fermionNumber, toggleFirst]
      have hset :
          (Finset.univ.filter fun x : Fin n =>
              if x = firstMode hn then w x = false else w x = true) =
            insert (firstMode hn) (Finset.univ.filter fun x : Fin n => w x = true) := by
        ext x
        by_cases hx : x = firstMode hn
        · subst hx
          simpa [Finset.mem_filter] using h0'
        · simp [hx, Finset.mem_filter]
      rw [hset]
      have hmem : firstMode hn ∉ Finset.univ.filter fun x : Fin n => w x = true := by
        simp [Finset.mem_filter, h0']
      simpa using Finset.card_insert_of_notMem hmem
    simpa [h0'] using hnum

lemma parity_flip_toggleFirst {n : ℕ} (hn : 0 < n) (w : Occupation n) :
    Even (fermionNumber (toggleFirst hn w)) ↔ ¬ Even (fermionNumber w) := by
  rw [fermionNumber_toggleFirst_eq_add_or_sub hn]
  by_cases h0 : w (firstMode hn) = false
  · simp [h0, Nat.even_add_one]
  · have h0' : w (firstMode hn) = true := Bool.eq_true_of_not_eq_false h0
    have hle : 1 ≤ fermionNumber w := by
      unfold fermionNumber
      rw [← Finset.card_filter]
      apply Finset.one_le_card.mpr
      exact ⟨firstMode hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩⟩
    have hs := Nat.even_sub (m := fermionNumber w) (n := 1) hle
    simpa [h0', Nat.not_even_iff_odd] using hs

/-- For every nonempty mode space, toggling one mode bijects the even and odd sectors. -/
theorem even_odd_card_equal_general {n : ℕ} (hn : 0 < n) :
    Fintype.card {w : Occupation n // Even (fermionNumber w)} =
      Fintype.card {w : Occupation n // ¬ Even (fermionNumber w)} := by
  let e : {w : Occupation n // Even (fermionNumber w)} ≃
      {w : Occupation n // ¬ Even (fermionNumber w)} :=
    { toFun := fun w => ⟨toggleFirst hn w.1, by
          intro hE
          exact (parity_flip_toggleFirst hn w.1).1 hE w.2⟩
      invFun := fun w => ⟨toggleFirst hn w.1, by
          exact (parity_flip_toggleFirst hn w.1).2 w.2⟩
      left_inv := by
        intro w
        apply Subtype.ext
        exact toggleFirst_involutive hn w.1
      right_inv := by
        intro w
        apply Subtype.ext
        exact toggleFirst_involutive hn w.1 }
  exact Fintype.card_congr e

/-- The even sector has `2^(n-1)` states for every positive mode count. -/
theorem card_even_general {n : ℕ} (hn : 0 < n) :
    Fintype.card {w : Occupation n // Even (fermionNumber w)} = 2 ^ (n - 1) := by
  have hEq := even_odd_card_equal_general hn
  have hcomp : Fintype.card {w : Occupation n // ¬ Even (fermionNumber w)} =
      2 ^ n - Fintype.card {w : Occupation n // Even (fermionNumber w)} := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
      (Fintype.card_subtype_compl (p := fun w : Occupation n => Even (fermionNumber w)))
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by omega
  omega

/-- The odd sector has `2^(n-1)` states for every positive mode count. -/
theorem card_odd_general {n : ℕ} (hn : 0 < n) :
    Fintype.card {w : Occupation n // ¬ Even (fermionNumber w)} = 2 ^ (n - 1) := by
  rw [← even_odd_card_equal_general hn]
  exact card_even_general hn

/-- The finite Witten index vanishes for every positive number of modes. -/
theorem witten_index_general {n : ℕ} (hn : 0 < n) :
    ((Fintype.card {w : Occupation n // Even (fermionNumber w)} : ℤ) -
      Fintype.card {w : Occupation n // ¬ Even (fermionNumber w)}) = 0 := by
  rw [card_even_general hn, card_odd_general hn]
  norm_num

/-! ### n = 0 — trivial vacuum -/

theorem n0_total : Fintype.card (Occupation 0) = 1 := by
  decide

theorem n0_fermionNumber (w : Occupation 0) : fermionNumber w = 0 := by
  simp [fermionNumber]

/-! ### n = 4 — the physical Cl(4,4) case -/

theorem n4_total : Fintype.card (Occupation 4) = 16 := by
  decide

theorem n4_even : Fintype.card {w : Occupation 4 // Even (fermionNumber w)} = 8 := by
  decide

theorem n4_odd : Fintype.card {w : Occupation 4 // ¬ Even (fermionNumber w)} = 8 := by
  decide

theorem n4_even_odd_equal :
    Fintype.card {w : Occupation 4 // Even (fermionNumber w)} =
    Fintype.card {w : Occupation 4 // ¬ Even (fermionNumber w)} := by
  rw [n4_even, n4_odd]

/-! ### Witten index -/

/-- Witten index vanishes for n=4: 8 - 8 = 0. -/
theorem witten_index_n4 : ((8 : ℤ) - 8) = 0 := by
  norm_num

end InfoGeometry.OperatorAlgebra.CliffordCARFockParity
