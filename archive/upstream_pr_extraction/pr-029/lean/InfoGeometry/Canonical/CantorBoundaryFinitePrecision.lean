import Mathlib.Tactic
import InfoGeometry.Canonical.CantorBoundaryReadoutBounds
import InfoGeometry.Canonical.CantorBoundaryFiniteReadout
import InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
import InfoGeometry.Canonical.CantorBoundaryComplexReadout

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryFinitePrecision

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
open InfoGeometry.Canonical.CantorBoundaryComplexReadout

/-- Real readout is stable under `N`-prefix agreement. -/
theorem real_readout_prefix_stability
    (N : ℕ) (w v : InfiniteBinaryWordSpace)
    (hprefix : ∀ n < N, w n = v n) :
    |realBinaryReadout w - realBinaryReadout v| ≤ (1 / 2 : ℝ) ^ N := by
  exact abs_realBinaryReadout_sub_le_of_prefix N w v hprefix

/-- Complex readout is stable under `N`-prefix agreement, with the same precision bound. -/
theorem complex_readout_prefix_stability
    (N : ℕ) (w v : InfiniteBinaryWordSpace)
    (hprefix : ∀ n < N, w n = v n) :
    ‖binaryReadout w - binaryReadout v‖ ≤ (1 / 2 : ℝ) ^ N := by
  have hreal :
      |realBinaryReadout w - realBinaryReadout v| ≤ (1 / 2 : ℝ) ^ N :=
    abs_realBinaryReadout_sub_le_of_prefix N w v hprefix
  calc
    ‖binaryReadout w - binaryReadout v‖
        = ‖((realBinaryReadout w - realBinaryReadout v : ℝ) : ℂ)‖ := by
          rw [complex_binaryReadout_eq_ofReal, complex_binaryReadout_eq_ofReal]
          simp
    _ = |(realBinaryReadout w - realBinaryReadout v : ℝ)| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
    _ ≤ (1 / 2 : ℝ) ^ N := hreal

/-- Prefix agreement puts values into a dyadic closed interval around the limit. -/
theorem real_readout_prefix_ball_mem
    (N : ℕ) (w v : InfiniteBinaryWordSpace)
    (hprefix : ∀ n < N, w n = v n) :
    realBinaryReadout v ∈ Set.Icc (realBinaryReadout w - (1 / 2 : ℝ) ^ N)
      (realBinaryReadout w + (1 / 2 : ℝ) ^ N) := by
  have hbound := real_readout_prefix_stability N w v hprefix
  rcases abs_le.mp hbound with ⟨h_lower, h_upper⟩
  constructor
  · linarith
  · linarith

/-- Same as `real_readout_prefix_stability` but via finite prefix approximants. -/
theorem readout_stability_via_partial_prefix
    (N : ℕ) (w v : InfiniteBinaryWordSpace)
    (hprefix : ∀ n < N, w n = v n) :
    |realBinaryReadout w - realBinaryPartialReadout N v| ≤
      (1 / 2 : ℝ) ^ N + |realBinaryPartialReadout N w - realBinaryPartialReadout N v| := by
  have hpart : realBinaryPartialReadout N w = realBinaryPartialReadout N v :=
    realBinaryPartialReadout_congr_of_prefix N w v hprefix
  have hnonneg : 0 ≤ realBinaryReadout w - realBinaryPartialReadout N w := by
    exact sub_nonneg.mpr (realBinaryPartialReadout_le_readout N w)
  have hw : |realBinaryReadout w - realBinaryPartialReadout N w| ≤ (1 / 2 : ℝ) ^ N := by
    simpa [abs_of_nonneg hnonneg] using
      (realBinaryReadout_sub_partial_le_half_pow N w)
  have hEq :
      realBinaryReadout w - realBinaryPartialReadout N v =
        (realBinaryReadout w - realBinaryPartialReadout N w) +
          (realBinaryPartialReadout N w - realBinaryPartialReadout N v) := by
    rw [hpart]
    ring
  rw [hEq]
  calc
    |(realBinaryReadout w - realBinaryPartialReadout N w) +
        (realBinaryPartialReadout N w - realBinaryPartialReadout N v)|
        ≤ |realBinaryReadout w - realBinaryPartialReadout N w| +
          |realBinaryPartialReadout N w - realBinaryPartialReadout N v| :=
      abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) ^ N + |realBinaryPartialReadout N w - realBinaryPartialReadout N v| := by
      linarith [hw]

end InfoGeometry.Canonical.CantorBoundaryFinitePrecision
