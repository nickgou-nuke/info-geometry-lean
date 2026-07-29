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
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout

theorem continuous_prefixBit (b : Bool) :
    Continuous (prefixBit b) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply n

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

theorem continuous_leftShift : Continuous (leftShift) := by
  exact continuous_prefixBit false

theorem continuous_rightShift : Continuous (rightShift) := by
  exact continuous_prefixBit true

theorem leftShift_injective : Function.Injective (leftShift) := by
  exact injective_prefixBit false

theorem rightShift_injective : Function.Injective (rightShift) := by
  exact injective_prefixBit true

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
