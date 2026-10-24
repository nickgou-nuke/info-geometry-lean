/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.NoncommRing

/-!
# Parity strings for commuting hard-core modes

The ambient ring is not commutative. Products use `Finset.noncommProd` with a
proved commutation witness, never a fictitious `CommMonoid` instance on the ring.
No star, division by two, or finite-dimensional representation is assumed.
-/
namespace InfoGeometry.Core.BosonParityString

variable {A : Type*} [Ring A] {N : ℕ}

/-- Local square-zero normalized pairs, commuting at distinct sites. -/
structure IsCommutingBosonSystem (d B : Fin N → A) : Prop where
  d_sq : ∀ j, d j * d j = 0
  B_sq : ∀ j, B j * B j = 0
  on_site : ∀ j, d j * B j + B j * d j = 1
  comm_dd : ∀ {j k}, j ≠ k → Commute (d j) (d k)
  comm_BB : ∀ {j k}, j ≠ k → Commute (B j) (B k)
  comm_dB : ∀ {j k}, j ≠ k → Commute (d j) (B k)

/-- Local parity, with the vacuum-first sign convention. -/
def parity (d B : Fin N → A) (j : Fin N) : A := d j * B j - B j * d j

/-- Select either local mode without duplicating the string arguments. -/
def mode (d B : Fin N → A) (c : Bool) (j : Fin N) : A := if c then B j else d j

namespace IsCommutingBosonSystem

variable {d B : Fin N → A} (h : IsCommutingBosonSystem d B)
include h

lemma local_actions (j : Fin N) :
    parity d B j * d j = d j ∧ d j * parity d B j = -d j ∧
    parity d B j * B j = -B j ∧ B j * parity d B j = B j := by
  have hd : d j * B j * d j = d j := by
    have H := congrArg (fun x => x * d j) (h.on_site j)
    simpa only [add_mul, mul_assoc, h.d_sq j, mul_zero, add_zero, one_mul] using H
  have hB : B j * d j * B j = B j := by
    have H := congrArg (fun x => x * B j) (h.on_site j)
    simpa only [add_mul, mul_assoc, h.B_sq j, mul_zero, zero_add, one_mul] using H
  unfold parity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sub_mul, hd, mul_assoc, h.d_sq j, mul_zero, sub_zero]
  · rw [mul_sub, ← mul_assoc, h.d_sq j, zero_mul, ← mul_assoc, hd, zero_sub]
  · rw [sub_mul, hB, mul_assoc, h.B_sq j, mul_zero, zero_sub]
  · rw [mul_sub, ← mul_assoc, hB, ← mul_assoc, h.B_sq j, zero_mul, sub_zero]

/-- The two standard formulas for the local parity agree. -/
lemma parity_eq_one_sub (j : Fin N) : parity d B j = 1 - 2 * (B j * d j) := by
  calc
    parity d B j = (d j * B j + B j * d j) - 2 * (B j * d j) := by
      unfold parity; noncomm_ring
    _ = 1 - 2 * (B j * d j) := by rw [h.on_site]

lemma parity_sq (j : Fin N) : parity d B j * parity d B j = 1 := by
  have H := h.local_actions j
  calc
    parity d B j * parity d B j =
        (parity d B j * d j) * B j - (parity d B j * B j) * d j := by
      unfold parity; noncomm_ring
    _ = 1 := by rw [H.1, H.2.2.1, neg_mul, sub_neg_eq_add, h.on_site j]

lemma mode_sq (c : Bool) (j : Fin N) : mode d B c j * mode d B c j = 0 := by
  cases c
  · exact h.d_sq j
  · exact h.B_sq j

lemma mode_commute (c e : Bool) {j k : Fin N} (hne : j ≠ k) :
    Commute (mode d B c j) (mode d B e k) := by
  cases c <;> cases e
  · exact h.comm_dd hne
  · exact h.comm_dB hne
  · exact (h.comm_dB hne.symm).symm
  · exact h.comm_BB hne

lemma parity_mode_commute (c : Bool) {j k : Fin N} (hne : j ≠ k) :
    Commute (parity d B j) (mode d B c k) := by
  exact ((h.mode_commute false c hne).mul_left (h.mode_commute true c hne)).sub_left
    ((h.mode_commute true c hne).mul_left (h.mode_commute false c hne))

lemma parity_commute (j k : Fin N) : Commute (parity d B j) (parity d B k) := by
  by_cases he : j = k
  · subst k; exact Commute.refl _
  exact ((h.parity_mode_commute false he).mul_right
    (h.parity_mode_commute true he)).sub_right
      ((h.parity_mode_commute true he).mul_right (h.parity_mode_commute false he))

lemma parity_mode_anti (c : Bool) (j : Fin N) :
    parity d B j * mode d B c j = -(mode d B c j * parity d B j) := by
  have H := h.local_actions j
  cases c
  · simp only [mode, Bool.false_eq_true, ↓reduceIte, H.1, H.2.1, neg_neg]
  · simp only [mode, ↓reduceIte, H.2.2.1, H.2.2.2]

/-- A product over any set of sites; pairwise commutation makes it order-independent. -/
def parityProduct (s : Finset (Fin N)) : A :=
  s.noncommProd (parity d B) (fun i _ j _ _ => h.parity_commute i j)

/-- The Jordan–Wigner prefix string, with no commutativity assumption on `A`. -/
def parityString (j : Fin N) : A := h.parityProduct (Finset.Iio j)

lemma product_commutes_parity (s : Finset (Fin N)) (j : Fin N) :
    Commute (h.parityProduct s) (parity d B j) :=
  (Finset.noncommProd_commute _ _ _ _ (fun i _ => h.parity_commute j i)).symm

lemma product_commute (s t : Finset (Fin N)) :
    Commute (h.parityProduct s) (h.parityProduct t) :=
  Finset.noncommProd_commute _ _ _ _ (fun j _ => h.product_commutes_parity s j)

lemma product_sq (s : Finset (Fin N)) : h.parityProduct s * h.parityProduct s = 1 := by
  let hc : (s : Set (Fin N)).Pairwise (fun i j => Commute (parity d B i) (parity d B j)) :=
    fun i _ j _ _ => h.parity_commute i j
  calc
    h.parityProduct s * h.parityProduct s =
        s.noncommProd (parity d B * parity d B)
          (Finset.noncommProd_mul_distrib_aux hc hc hc) :=
      (Finset.noncommProd_mul_distrib (s := s) (parity d B) (parity d B) hc hc hc).symm
    _ = 1 ^ s.card :=
      Finset.noncommProd_eq_pow_card s (parity d B * parity d B) _ 1
        (fun i _ => h.parity_sq i)
    _ = 1 := one_pow _

lemma product_mode_commute (s : Finset (Fin N)) (c : Bool) (j : Fin N) (hj : j ∉ s) :
    Commute (h.parityProduct s) (mode d B c j) := by
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro k hk
  exact (h.parity_mode_commute c (ne_of_mem_of_not_mem hk hj)).symm

lemma product_mode_anti (s : Finset (Fin N)) (c : Bool) (j : Fin N) (hj : j ∈ s) :
    h.parityProduct s * mode d B c j = -(mode d B c j * h.parityProduct s) := by
  have split : h.parityProduct s = h.parityProduct (s.erase j) * parity d B j :=
    (Finset.noncommProd_erase_mul s hj _ _).symm
  have hc := h.product_mode_commute (s.erase j) c j (Finset.notMem_erase j s)
  rw [split, mul_assoc, h.parity_mode_anti c j, mul_neg, ← mul_assoc, hc.eq]
  simp only [mul_assoc]

lemma string_sq (j : Fin N) : h.parityString j * h.parityString j = 1 :=
  h.product_sq _

lemma string_mode_commute (c : Bool) {j k : Fin N} (hle : j ≤ k) :
    Commute (h.parityString j) (mode d B c k) :=
  h.product_mode_commute _ c k (by simpa using not_lt_of_ge hle)

lemma string_mode_anti (c : Bool) {j k : Fin N} (hlt : k < j) :
    h.parityString j * mode d B c k = -(mode d B c k * h.parityString j) :=
  h.product_mode_anti _ c k (Finset.mem_Iio.mpr hlt)

/-- The dressed mode; `false` is annihilation, `true` is creation. -/
def dressed (c : Bool) (j : Fin N) : A := h.parityString j * mode d B c j

lemma dressed_mul_same (c e : Bool) (j : Fin N) :
    h.dressed c j * h.dressed e j = mode d B c j * mode d B e j := by
  unfold dressed
  rw [mul_assoc, ← mul_assoc (mode d B c j), ← (h.string_mode_commute c le_rfl).eq,
    ← mul_assoc]
  simp only [← mul_assoc, h.string_sq, one_mul]

lemma dressed_sq (c : Bool) (j : Fin N) : h.dressed c j * h.dressed c j = 0 := by
  rw [h.dressed_mul_same, h.mode_sq]

lemma dressed_anti_of_lt (c e : Bool) {j k : Fin N} (hlt : j < k) :
    h.dressed c j * h.dressed e k = -(h.dressed e k * h.dressed c j) := by
  have hs := (h.product_commute (Finset.Iio j) (Finset.Iio k)).eq
  change h.parityString j * h.parityString k = h.parityString k * h.parityString j at hs
  have ha : mode d B c j * h.parityString k = -(h.parityString k * mode d B c j) := by
    rw [h.string_mode_anti c hlt, neg_neg]
  unfold dressed
  calc
    (h.parityString j * mode d B c j) * (h.parityString k * mode d B e k) =
        -(h.parityString j * h.parityString k * (mode d B c j * mode d B e k)) := by
      rw [mul_assoc, ← mul_assoc (mode d B c j), ha]; noncomm_ring
    _ = -(h.parityString k * h.parityString j * (mode d B e k * mode d B c j)) := by
      rw [hs, (h.mode_commute c e (ne_of_lt hlt)).eq]
    _ = -((h.parityString k * mode d B e k) * (h.parityString j * mode d B c j)) := by
      rw [mul_assoc (h.parityString k), ← mul_assoc (h.parityString j),
        (h.string_mode_commute e hlt.le).eq]
      simp only [mul_assoc]

lemma dressed_anti (c e : Bool) {j k : Fin N} (hne : j ≠ k) :
    h.dressed c j * h.dressed e k + h.dressed e k * h.dressed c j = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [h.dressed_anti_of_lt c e hlt, neg_add_cancel]
  · rw [h.dressed_anti_of_lt e c hgt, add_neg_cancel]

lemma dressed_self_car (c : Bool) (j k : Fin N) :
    h.dressed c j * h.dressed c k + h.dressed c k * h.dressed c j = 0 := by
  by_cases he : j = k
  · subst k; rw [h.dressed_sq, zero_add]
  · exact h.dressed_anti c c he

lemma dressed_mixed_car (j k : Fin N) :
    h.dressed false j * h.dressed true k + h.dressed true k * h.dressed false j =
      if j = k then 1 else 0 := by
  by_cases he : j = k
  · subst k; simp only [h.dressed_mul_same, ↓reduceIte]; exact h.on_site j
  · rw [ite_eq_right_iff.mpr (fun he' => (he he').elim)]; exact h.dressed_anti false true he

/-- Local products, and hence both support projections and parity, survive dressing. -/
lemma dressed_parity (j : Fin N) :
    h.dressed false j * h.dressed true j - h.dressed true j * h.dressed false j =
      parity d B j := by
  rw [h.dressed_mul_same, h.dressed_mul_same]; rfl

/-- Genuine mode recovery; recovering parity alone is not an inverse on modes. -/
lemma undress (c : Bool) (j : Fin N) :
    h.parityString j * h.dressed c j = mode d B c j := by
  rw [dressed, ← mul_assoc, h.string_sq, one_mul]

/-- Reconstruct the prefix using only the output pair's local commutators. -/
def recoveredString (j : Fin N) : A :=
  (Finset.Iio j).noncommProd (parity (h.dressed false) (h.dressed true))
    (fun i _ k _ _ => by
      change Commute (h.dressed false i * h.dressed true i - h.dressed true i * h.dressed false i)
        (h.dressed false k * h.dressed true k - h.dressed true k * h.dressed false k)
      rw [h.dressed_parity, h.dressed_parity]
      exact h.parity_commute i k)

lemma recoveredString_eq (j : Fin N) : h.recoveredString j = h.parityString j :=
  Finset.noncommProd_congr rfl (fun i _ => h.dressed_parity i) _

/-- Both original generators are recovered from the output pair, without division by two. -/
lemma recover_modes (c : Bool) (j : Fin N) :
    h.recoveredString j * h.dressed c j = mode d B c j := by
  rw [h.recoveredString_eq, h.undress]

end IsCommutingBosonSystem
end InfoGeometry.Core.BosonParityString
