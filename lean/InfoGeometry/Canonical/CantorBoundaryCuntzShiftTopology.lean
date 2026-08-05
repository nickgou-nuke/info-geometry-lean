import Mathlib.Topology.Constructions
import InfoGeometry.Canonical.CantorBoundaryCuntzShift
import InfoGeometry.Canonical.CantorBoundaryFiniteReadout

/-!
# Product-topology facts for the two symbolic Cuntz branches

The front-prefix maps are the finite-cylinder maps underlying the two symbolic
branches.  This owner records only their native topological and readout facts:
continuity, injectivity, disjoint branch images, and the affine recursion of
the binary readout.
-/

noncomputable section

open scoped Topology BigOperators

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout

theorem continuous_prefixBit (b : Bool) :
    Continuous (prefixBit b) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply n

theorem continuous_boundaryHead :
    Continuous (boundaryHead : CantorBoundary → Bool) := by
  exact continuous_apply 0

theorem continuous_boundaryTail :
    Continuous (boundaryTail : CantorBoundary → CantorBoundary) := by
  apply continuous_pi
  intro n
  exact continuous_apply (n + 1)

theorem boundaryTail_prefixBit (b : Bool) (x : CantorBoundary) :
    boundaryTail (prefixBit b x) = x := by
  funext n
  rfl

theorem injective_prefixBit (b : Bool) :
    Function.Injective (prefixBit b) := by
  intro x y h
  funext n
  exact congrFun h (n + 1)

theorem left_right_branch_images_disjoint
    (x y : CantorBoundary) :
    prefixBit false x ≠ prefixBit true y := by
  intro h
  have hzero := congrFun h 0
  simp [prefixBit] at hzero

theorem prefixBit_head_tail_topology (x : CantorBoundary) :
    prefixBit (boundaryHead x) (boundaryTail x) = x := by
  simpa [prefixBit] using (boundary_recursive_decomposition x).symm

theorem prefixBit_range_cover_topology (x : CantorBoundary) :
    (∃ y, prefixBit false y = x) ∨ ∃ y, prefixBit true y = x := by
  cases h : boundaryHead x with
  | false =>
      left
      exact ⟨boundaryTail x, by simpa [h] using prefixBit_head_tail_topology x⟩
  | true =>
      right
      exact ⟨boundaryTail x, by simpa [h] using prefixBit_head_tail_topology x⟩

theorem realBinaryReadout_prefixBit
    (b : Bool) (x : CantorBoundary) :
    realBinaryReadout (prefixBit b x) =
      (if b then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) * realBinaryReadout x := by
  exact realBinaryReadout_boundaryCons b x

theorem realBinaryReadout_leftShift
    (x : CantorBoundary) :
    realBinaryReadout (leftShift x) =
      (1 / 2 : ℝ) * realBinaryReadout x := by
  simpa [leftShift] using realBinaryReadout_prefixBit false x

theorem realBinaryReadout_rightShift
    (x : CantorBoundary) :
    realBinaryReadout (rightShift x) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * realBinaryReadout x := by
  simpa [rightShift] using realBinaryReadout_prefixBit true x

end InfoGeometry.Canonical.CantorBoundaryCuntzShift
