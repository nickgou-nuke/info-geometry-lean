/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# Canonical binary representatives

The binary expansion is made canonical by excluding words that are eventually
constant equal to `true`.  This is the exact ambiguity condition for the usual
binary expansion; no injectivity theorem is asserted here yet.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryCanonical

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

def CanonicalBinaryWord (w : InfiniteBinaryWordSpace) : Prop :=
  ¬ ∃ N, ∀ n ≥ N, w n = true

theorem canonicalBinaryWord_iff (w : InfiniteBinaryWordSpace) :
    CanonicalBinaryWord w ↔ ¬ ∃ N, ∀ n ≥ N, w n = true := by
  rfl

theorem canonicalBinaryWord_of_arbitrarily_late_false
    (w : InfiniteBinaryWordSpace)
    (h : ∀ N, ∃ n ≥ N, w n = false) :
    CanonicalBinaryWord w := by
  intro h_eventual
  obtain ⟨N, hN⟩ := h_eventual
  obtain ⟨n, hn, hn_false⟩ := h N
  have hn_true : w n = true := hN n hn
  simp [hn_false] at hn_true

theorem canonicalBinaryWord_zero
    (w : InfiniteBinaryWordSpace)
    (h : ∀ n, w n = false) :
    CanonicalBinaryWord w := by
  apply canonicalBinaryWord_of_arbitrarily_late_false
  intro N
  exact ⟨N, le_rfl, h N⟩

theorem exists_first_binary_difference
    {w v : InfiniteBinaryWordSpace}
    (h : w ≠ v) :
    ∃ k, (∀ n < k, w n = v n) ∧ w k ≠ v k := by
  have hex : ∃ n, w n ≠ v n := by
    by_contra hnone
    apply h
    funext n
    by_contra hne
    exact hnone ⟨n, hne⟩
  let k : ℕ := Nat.find hex
  have hk : w k ≠ v k := Nat.find_spec hex
  refine ⟨k, ?_, hk⟩
  intro n hn
  by_contra hne
  exact (Nat.find_min hex hn) hne

/-- The subtype of words selected for the canonical `[0,1)` lane. -/
abbrev CanonicalBinaryWordSpace :=
  {w : (ℕ → Bool) // CanonicalBinaryWord w}


theorem canonicalBinaryWord_iff_arbitrarily_late_false
    (w : (ℕ → Bool)) :
    CanonicalBinaryWord w ↔ ∀ N, ∃ n ≥ N, w n = false := by
  constructor
  · intro hw N
    by_contra hnone
    push_neg at hnone
    apply hw
    refine ⟨N, ?_⟩
    intro n hn
    cases hbit : w n with
    | false => exact False.elim (hnone n hn hbit)
    | true => rfl
  · exact canonicalBinaryWord_of_arbitrarily_late_false w


theorem canonicalBinaryWordSpace_arbitrarily_late_false
    (w : CanonicalBinaryWordSpace) :
    ∀ N, ∃ n ≥ N, w.1 n = false :=
  (canonicalBinaryWord_iff_arbitrarily_late_false w.1).mp w.2


theorem canonicalBinaryWord_boundaryCons
    (b : Bool) (w : (ℕ → Bool))
    (hw : CanonicalBinaryWord w) :
    CanonicalBinaryWord (boundaryCons b w) := by
  apply (canonicalBinaryWord_iff_arbitrarily_late_false _).2
  intro N
  obtain ⟨n, hn, hfalse⟩ :=
    (canonicalBinaryWord_iff_arbitrarily_late_false w).1 hw (N + 1)
  refine ⟨n + 1, by omega, ?_⟩
  simpa [boundaryCons] using hfalse


theorem canonicalBinaryWord_boundaryTail
    (w : (ℕ → Bool))
    (hw : CanonicalBinaryWord w) :
    CanonicalBinaryWord (boundaryTail w) := by
  apply (canonicalBinaryWord_iff_arbitrarily_late_false _).2
  intro N
  obtain ⟨n, hn, hfalse⟩ :=
    (canonicalBinaryWord_iff_arbitrarily_late_false w).1 hw (N + 1)
  refine ⟨n - 1, by omega, ?_⟩
  have hindex : n - 1 + 1 = n := by omega
  simpa [boundaryTail, hindex] using hfalse


theorem canonicalBinaryWord_boundaryCons_iff
    (b : Bool) (w : (ℕ → Bool)) :
    CanonicalBinaryWord (boundaryCons b w) ↔
      CanonicalBinaryWord w := by
  constructor
  · intro h
    have htail := canonicalBinaryWord_boundaryTail (boundaryCons b w) h
    simpa [boundaryCons, boundaryTail] using htail
  · exact canonicalBinaryWord_boundaryCons b w


theorem canonicalBinaryWord_boundaryTail_iff
    (w : (ℕ → Bool)) :
    CanonicalBinaryWord (boundaryTail w) ↔
      CanonicalBinaryWord w := by
  rw [boundary_recursive_decomposition w]
  exact (canonicalBinaryWord_boundaryCons_iff
    (boundaryHead w) (boundaryTail w)).symm


theorem not_canonicalBinaryWord_iff
    (w : (ℕ → Bool)) :
    ¬ CanonicalBinaryWord w ↔ ∃ N, ∀ n ≥ N, w n = true := by
  simp [CanonicalBinaryWord]

end InfoGeometry.Canonical.CantorBoundaryCanonical
