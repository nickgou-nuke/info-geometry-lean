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
    (a : Bool) (w : InfiniteBinaryWordSpace) :
    boundaryHead (boundaryCons a w) = a := by
  rfl

@[simp] theorem boundaryTail_boundaryCons
    (a : Bool) (w : InfiniteBinaryWordSpace) :
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
    (w v : InfiniteBinaryWordSpace) :
    boundaryCons false w ≠ boundaryCons true v := by
  intro h
  have hzero := congrFun h 0
  simpa [boundaryCons] using hzero

theorem boundaryCons_true_ne_false
    (w v : InfiniteBinaryWordSpace) :
    boundaryCons true w ≠ boundaryCons false v := by
  intro h
  have hzero := congrFun h 0
  simpa [boundaryCons] using hzero

theorem boundaryCons_boundaryHead_tail
    (x : InfiniteBinaryWordSpace) :
    boundaryCons (boundaryHead x) (boundaryTail x) = x := by
  exact (boundary_recursive_decomposition x).symm

theorem boundaryCons_eq_iff
    (a b : Bool) (w v : InfiniteBinaryWordSpace) :
    boundaryCons a w = boundaryCons b v ↔ a = b ∧ w = v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact congrFun h 0
    · simpa using congrArg boundaryTail h
  · rintro ⟨rfl, rfl⟩
    rfl

end InfoGeometry.Canonical.CantorBoundaryBranchLemmas
