import Mathlib.Tactic
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# Binary branch embeddings

These lemmas formalize the finite symbolic branch maps on the existing Cantor
boundary carrier.  They do not assert a C*-algebraic or spectral duality.
-/

namespace InfoGeometry.Canonical.CantorBoundaryBranchLemmas

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

@[simp] theorem boundaryHead_boundaryCons
    (a : Bool) (w : (ℕ → Bool)) :
    boundaryHead (boundaryCons a w) = a := by
  rfl

@[simp] theorem boundaryTail_boundaryCons
    (a : Bool) (w : (ℕ → Bool)) :
    boundaryTail (boundaryCons a w) = w := by
  funext n
  rfl

theorem boundaryCons_injective (a : Bool) :
    Function.Injective (boundaryCons a) := by
  intro w v h
  funext n
  have hn := congrFun h (n + 1)
  simpa [boundaryCons] using hn

theorem boundaryCons_false_ne_true
    (w v : (ℕ → Bool)) :
    boundaryCons false w ≠ boundaryCons true v := by
  intro h
  have hzero := congrFun h 0
  simpa [boundaryCons] using hzero

theorem boundaryCons_true_ne_false
    (w v : (ℕ → Bool)) :
    boundaryCons true w ≠ boundaryCons false v := by
  intro h
  have hzero := congrFun h 0
  simpa [boundaryCons] using hzero

theorem boundaryCons_boundaryHead_tail
    (x : (ℕ → Bool)) :
    boundaryCons (boundaryHead x) (boundaryTail x) = x := by
  exact (boundary_recursive_decomposition x).symm

theorem boundaryCons_eq_iff
    (a b : Bool) (w v : (ℕ → Bool)) :
    boundaryCons a w = boundaryCons b v ↔ a = b ∧ w = v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact congrFun h 0
    · simpa using congrArg boundaryTail h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem boundaryCons_range_false_disjoint_true :
    Set.range (boundaryCons false) ∩ Set.range (boundaryCons true) = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨w, rfl⟩, v, h⟩
    exact False.elim (boundaryCons_false_ne_true w v h.symm)
  · simp

theorem boundaryCons_range_true_disjoint_false :
    Set.range (boundaryCons true) ∩ Set.range (boundaryCons false) = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨w, rfl⟩, v, h⟩
    exact False.elim (boundaryCons_true_ne_false w v h.symm)
  · simp

theorem boundaryCons_range_false_union_true :
    Set.range (boundaryCons false) ∪ Set.range (boundaryCons true) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    by_cases h : boundaryHead x = false
    · left
      exact ⟨boundaryTail x, by
        calc
          boundaryCons false (boundaryTail x) =
              boundaryCons (boundaryHead x) (boundaryTail x) := by rw [h]
          _ = x := boundaryCons_boundaryHead_tail x⟩
    · right
      have hx : boundaryHead x = true := Bool.eq_true_of_not_eq_false h
      exact ⟨boundaryTail x, by
        calc
          boundaryCons true (boundaryTail x) =
              boundaryCons (boundaryHead x) (boundaryTail x) := by rw [hx]
          _ = x := boundaryCons_boundaryHead_tail x⟩

theorem boundaryCons_range_partition :
    Disjoint (Set.range (boundaryCons false)) (Set.range (boundaryCons true)) ∧
      Set.range (boundaryCons false) ∪ Set.range (boundaryCons true) = Set.univ := by
  constructor
  · refine Set.disjoint_left.2 ?_
    intro x hx hy
    rcases hx with ⟨w, hw⟩
    rcases hy with ⟨v, hv⟩
    exact boundaryCons_false_ne_true w v (hw.trans hv.symm)
  · exact boundaryCons_range_false_union_true

end InfoGeometry.Canonical.CantorBoundaryBranchLemmas
