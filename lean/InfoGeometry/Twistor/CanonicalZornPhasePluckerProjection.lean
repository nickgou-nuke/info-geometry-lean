import InfoGeometry.Twistor.PhaseNativePluckerBridge
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Canonical Zorn projection to the native phase/Plücker readout

This file records only the coordinate projection carried by the canonical Zorn
cell.  The diagonal coordinates are retained separately; consequently this is
not an equivalence with the six-dimensional phase carrier.
-/

namespace InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
open InfoGeometry.Twistor.PhaseNativePluckerBridge
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ

def offDiagonalPhase (X : CanonicalZorn) : Phase := (X.x, X.y)

theorem kleinQ_offDiagonalPhase (X : CanonicalZorn) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) =
      InfoGeometry.Canonical.ZornMatrix.dot X.x X.y := by
  simpa [offDiagonalPhase, chiralPairing] using
    (kleinQ_phaseToPlucker6 (offDiagonalPhase X))

theorem detZ_eq_diagonal_sub_kleinQ (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X =
      X.a * X.b -
        InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (phaseToPlucker6 (offDiagonalPhase X)) := by
  rw [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    kleinQ_offDiagonalPhase]

theorem detZ_eq_zero_iff_diagonal_eq_kleinQ (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 ↔
      X.a * X.b =
        InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (phaseToPlucker6 (offDiagonalPhase X)) := by
  rw [detZ_eq_diagonal_sub_kleinQ]
  exact sub_eq_zero

end InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection
