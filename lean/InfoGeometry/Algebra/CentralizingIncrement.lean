/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-! Centralizing increments characterize exact commutator transport through
an arbitrary unital ring homomorphism. No characteristic assumption is used. -/

namespace InfoGeometry.Algebra.CentralizingIncrement

/-- Strict commutator transport at one element is exactly centralization by
its Hamiltonian increment. No characteristic assumption is needed. -/
theorem commutator_map_eq_iff {A B : Type*} [Ring A] [Ring B]
    (e : A →+* B) (H : A) (K : B) (a : A) :
    K * e a - e a * K = e (H * a - a * H) ↔
      Commute (K - e H) (e a) := by
  have hd : (K - e H) * e a - e a * (K - e H) =
      (K * e a - e a * K) - e (H * a - a * H) := by
    simp only [map_sub, map_mul]
    noncomm_ring
  constructor
  · intro h
    change (K - e H) * e a = e a * (K - e H)
    apply sub_eq_zero.mp
    rw [hd, h, sub_self]
  · intro h
    apply sub_eq_zero.mp
    rw [← hd]
    exact sub_eq_zero.mpr h.eq

/-- Compatibility on the entire old algebra is equivalent to its increment
belonging to the relative commutant, expressed without a new carrier. -/
theorem commutator_compatible_iff {A B : Type*} [Ring A] [Ring B]
    (e : A →+* B) (H : A) (K : B) :
    (∀ a, K * e a - e a * K = e (H * a - a * H)) ↔
      ∀ a, Commute (K - e H) (e a) := by
  exact forall_congr' (fun a => commutator_map_eq_iff e H K a)

end InfoGeometry.Algebra.CentralizingIncrement
