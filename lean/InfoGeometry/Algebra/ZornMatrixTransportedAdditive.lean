import InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge

namespace InfoGeometry.Algebra.ZornMatrixTransportedAdditive

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge

/-! The legacy carrier is given additive structure only through transport.
This file intentionally does not install instances: it exposes the exact laws
needed by downstream adapters without changing the legacy typeclass graph. -/

theorem add_assoc_readout (X Y Z : ZornMatrix ℝ) :
    oldToVector ((X + Y) + Z) =
      oldToVector (X + (Y + Z)) := by
  simpa only [oldToVector_add] using
    (InfoGeometry.Algebra.ZornVectorMatrix.add_assoc (R := ℝ)
      (oldToVector X) (oldToVector Y) (oldToVector Z))

theorem zero_add_readout (X : ZornMatrix ℝ) :
    oldToVector (0 + X) = oldToVector X := by
  simpa only [oldToVector_add, oldToVector_zero] using
    (InfoGeometry.Algebra.ZornVectorMatrix.zero_add (R := ℝ) (oldToVector X))

theorem add_zero_readout (X : ZornMatrix ℝ) :
    oldToVector (X + 0) = oldToVector X := by
  simpa only [oldToVector_add, oldToVector_zero] using
    (InfoGeometry.Algebra.ZornVectorMatrix.add_zero (R := ℝ) (oldToVector X))

theorem add_comm_readout (X Y : ZornMatrix ℝ) :
    oldToVector (X + Y) = oldToVector (Y + X) := by
  simpa only [oldToVector_add] using
    (InfoGeometry.Algebra.ZornVectorMatrix.add_comm (R := ℝ)
      (oldToVector X) (oldToVector Y))

theorem smul_add_readout (r : ℝ) (X Y : ZornMatrix ℝ) :
    oldToVector (r • (X + Y)) =
      oldToVector (r • X + r • Y) := by
  simpa only [oldToVector_smul, oldToVector_add] using
    (InfoGeometry.Algebra.ZornVectorMatrix.smul_add (R := ℝ)
      r (oldToVector X) (oldToVector Y))

theorem add_smul_readout (r s : ℝ) (X : ZornMatrix ℝ) :
    oldToVector ((r + s) • X) =
      oldToVector (r • X + s • X) := by
  simpa only [oldToVector_smul, oldToVector_add] using
    (InfoGeometry.Algebra.ZornVectorMatrix.add_smul (R := ℝ)
      r s (oldToVector X))

end InfoGeometry.Algebra.ZornMatrixTransportedAdditive
