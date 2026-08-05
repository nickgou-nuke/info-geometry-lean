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

theorem complex_binaryReadout_im
    (w : InfiniteBinaryWordSpace) :
    (binaryReadout w).im = 0 := by
  rw [complex_binaryReadout_eq_ofReal]
  rfl

theorem complex_binaryReadout_mem_real_unitInterval
    (w : InfiniteBinaryWordSpace) :
    (binaryReadout w).re ∈ Set.Icc (0 : ℝ) 1 := by
  rw [complex_binaryReadout_re]
  exact realBinaryReadout_mem_unitInterval w

theorem complex_binaryReadout_norm_le_one
    (w : InfiniteBinaryWordSpace) :
    ‖binaryReadout w‖ ≤ 1 := by
  rw [complex_binaryReadout_eq_ofReal]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realBinaryReadout_nonnegative w)]
  exact realBinaryReadout_le_one w

theorem complex_binaryReadout_norm_eq_real
    (w : InfiniteBinaryWordSpace) :
    ‖binaryReadout w‖ = realBinaryReadout w := by
  rw [complex_binaryReadout_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realBinaryReadout_nonnegative w)]

theorem realBinaryReadout_complement
    (w : InfiniteBinaryWordSpace) :
    realBinaryReadout (fun n => !w n) + realBinaryReadout w = 1 := by
  have h := congrArg Complex.re (binary_readout_complement w)
  simpa [complex_binaryReadout_re] using h

theorem realBinaryReadout_complement_eq_one_sub
    (w : InfiniteBinaryWordSpace) :
    realBinaryReadout (fun n => !w n) = 1 - realBinaryReadout w := by
  exact (eq_sub_iff_add_eq).2 (realBinaryReadout_complement w)

theorem complex_binaryReadout_complement_eq_one_sub
    (w : InfiniteBinaryWordSpace) :
    binaryReadout (fun n => !w n) = 1 - binaryReadout w := by
  exact (eq_sub_iff_add_eq).2 (binary_readout_complement w)

end InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
