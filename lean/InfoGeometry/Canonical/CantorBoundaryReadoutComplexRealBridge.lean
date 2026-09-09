import InfoGeometry.Canonical.CantorBoundaryComplexReadout
import InfoGeometry.Canonical.CantorBoundaryReadoutBounds

/-!
# Real/complex compatibility of the binary Cantor readout

The complex readout is exactly the complexification of the real readout.  This
is the bridge needed to transport the unit-interval bounds without claiming
any additional embedding theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryComplexReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds

theorem complex_binaryReadout_eq_ofReal
    (w : InfiniteBinaryWordSpace) :
    binaryReadout w = (realBinaryReadout w : ℂ) := by
  rw [binaryReadout, realBinaryReadout, Complex.ofReal_tsum]
  congr 1
  funext n
  dsimp [binaryTerm, realBinaryTerm, binaryDigit]
  split <;> simp [Complex.ofReal_mul]

theorem complex_binaryReadout_re
    (w : InfiniteBinaryWordSpace) :
    (binaryReadout w).re = realBinaryReadout w := by
  rw [complex_binaryReadout_eq_ofReal]
  rfl

theorem complex_binaryReadout_mem_real_unitInterval
    (w : InfiniteBinaryWordSpace) :
    (binaryReadout w).re ∈ Set.Icc (0 : ℝ) 1 := by
  rw [complex_binaryReadout_re]
  exact realBinaryReadout_mem_unitInterval w

end InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
