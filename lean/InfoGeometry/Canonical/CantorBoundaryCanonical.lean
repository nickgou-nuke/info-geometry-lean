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

end InfoGeometry.Canonical.CantorBoundaryCanonical
