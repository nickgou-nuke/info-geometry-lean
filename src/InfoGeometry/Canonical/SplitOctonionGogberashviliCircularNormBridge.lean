import InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Gogberashvili signal norm in circular Peirce coordinates

The signal-coordinate norm from arXiv:1506.01012 is identified with the
determinant norm of the canonical Zorn realization and then read in the
circular Peirce basis.  This is a comparison theorem only: it introduces no
new carrier or physical interpretation.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionGogberashviliCircularNormBridge

open InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge
open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

theorem signalNorm_eq_circularPeirce_det
    (c : ℝ) (s : SignalCoordinates) :
    signalNorm c s =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        realCrossProduct3
        (paperCanonicalLinearEquiv (toNativeZorn c s)) := by
  calc
    signalNorm c s = zornNorm (toNativeZorn c s) :=
      (native_zorn_norm_eq_signalNorm c s).symm
    _ = InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        realCrossProduct3
        (paperCanonicalLinearEquiv (toNativeZorn c s)) :=
      paperCanonicalLinearEquiv_norm (toNativeZorn c s)

theorem signalNorm_eq_circularPeirce_formula
    (c : ℝ) (s : SignalCoordinates) :
    signalNorm c s =
      circularCoordinate
          (cartesianZornLinearEquiv.symm
            (paperCanonicalLinearEquiv (toNativeZorn c s))) 0 *
          circularCoordinate
          (cartesianZornLinearEquiv.symm
            (paperCanonicalLinearEquiv (toNativeZorn c s))) 4 -
        (circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 1 *
            circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 5 +
          circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 2 *
            circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 6 +
          circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 3 *
            circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 7) := by
  rw [signalNorm_eq_circularPeirce_det]
  exact circularPeirceBasis_norm_formula
    (paperCanonicalLinearEquiv (toNativeZorn c s))

theorem isZeroNorm_iff_circularPeirce_formula
    (c : ℝ) (s : SignalCoordinates) :
    IsZeroNorm c s ↔
      circularCoordinate
          (cartesianZornLinearEquiv.symm
            (paperCanonicalLinearEquiv (toNativeZorn c s))) 0 *
          circularCoordinate
          (cartesianZornLinearEquiv.symm
            (paperCanonicalLinearEquiv (toNativeZorn c s))) 4 =
        circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 1 *
            circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 5 +
          circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 2 *
            circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 6 +
          circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 3 *
            circularCoordinate
            (cartesianZornLinearEquiv.symm
              (paperCanonicalLinearEquiv (toNativeZorn c s))) 7 := by
  change signalNorm c s = 0 ↔ _
  rw [signalNorm_eq_circularPeirce_formula]
  constructor <;> intro h
  · linarith
  · linarith

theorem signalNorm_eq_appendixD_circular_formula
    (c : ℝ) (s : SignalCoordinates) :
    signalNorm c s =
      (s.omega + c * s.time) * (s.omega - c * s.time) -
        ((s.lambda 0 - s.position 0) * (s.lambda 0 + s.position 0) +
          (s.lambda 1 - s.position 1) * (s.lambda 1 + s.position 1) +
          (s.lambda 2 - s.position 2) * (s.lambda 2 + s.position 2)) := by
  simp [signalNorm]
  ring

theorem isZeroNorm_iff_appendixD_circular_formula
    (c : ℝ) (s : SignalCoordinates) :
    IsZeroNorm c s ↔
      (s.omega + c * s.time) * (s.omega - c * s.time) =
        (s.lambda 0 - s.position 0) * (s.lambda 0 + s.position 0) +
          (s.lambda 1 - s.position 1) * (s.lambda 1 + s.position 1) +
          (s.lambda 2 - s.position 2) * (s.lambda 2 + s.position 2) := by
  change signalNorm c s = 0 ↔ _
  rw [signalNorm_eq_appendixD_circular_formula]
  constructor <;> intro h <;> linarith

end InfoGeometry.Canonical.SplitOctonionGogberashviliCircularNormBridge
