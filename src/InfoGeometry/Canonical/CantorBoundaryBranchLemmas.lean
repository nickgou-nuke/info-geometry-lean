import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# Binary branch embeddings

These lemmas formalize the finite symbolic branch maps on the existing Cantor
boundary carrier.  They do not assert a C*-algebraic or spectral duality.
-/

namespace InfoGeometry.Canonical.CantorBoundaryBranchLemmas

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

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

end InfoGeometry.Canonical.CantorBoundaryBranchLemmas
