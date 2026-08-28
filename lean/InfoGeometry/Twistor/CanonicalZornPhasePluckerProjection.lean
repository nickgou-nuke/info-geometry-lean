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

theorem offDiagonalPhase_circular_coordinates (X : CanonicalZorn) (i : Fin 3) :
    X.x i =
      circularCoordinate (cartesianZornLinearEquiv.symm X)
        ⟨i.val + 1, by omega⟩ ∧
    X.y i =
      circularCoordinate (cartesianZornLinearEquiv.symm X)
        ⟨i.val + 5, by omega⟩ := by
  rcases X with ⟨a, b, x, y⟩
  fin_cases i <;>
    simp [cartesianZornLinearEquiv_symm_apply, circularCoordinate] <;>
    constructor <;> ring

theorem kleinQ_offDiagonalPhase (X : CanonicalZorn) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) =
      InfoGeometry.Canonical.ZornMatrix.dot X.x X.y := by
  simpa [offDiagonalPhase, chiralPairing] using
    (kleinQ_phaseToPlucker6 (offDiagonalPhase X))

theorem kleinNull_offDiagonalPhase_iff (X : CanonicalZorn) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) = 0 ↔
      InfoGeometry.Canonical.ZornMatrix.dot X.x X.y = 0 := by
  rw [kleinQ_offDiagonalPhase]

theorem phaseToPlucker6_offDiagonalPhase (X : CanonicalZorn) :
    phaseToPlucker6 (offDiagonalPhase X) =
      { p01 := X.x 0
        p02 := X.x 1
        p03 := X.x 2
        p12 := X.y 2
        p13 := -X.y 1
        p23 := X.y 0 } := by
  rfl

theorem phaseToPlucker6_offDiagonalPhase_circular (X : CanonicalZorn) :
    phaseToPlucker6 (offDiagonalPhase X) =
      { p01 := circularCoordinate (cartesianZornLinearEquiv.symm X) 1
        p02 := circularCoordinate (cartesianZornLinearEquiv.symm X) 2
        p03 := circularCoordinate (cartesianZornLinearEquiv.symm X) 3
        p12 := circularCoordinate (cartesianZornLinearEquiv.symm X) 7
        p13 := -circularCoordinate (cartesianZornLinearEquiv.symm X) 6
        p23 := circularCoordinate (cartesianZornLinearEquiv.symm X) 5 } := by
  rcases X with ⟨a, b, x, y⟩
  ext <;>
    simp [offDiagonalPhase, phaseToPlucker6,
      cartesianZornLinearEquiv_symm_apply, circularCoordinate] <;>
    ring

theorem offDiagonalPhase_pluckerLine_of_null
    (X : CanonicalZorn)
    (hnull : InfoGeometry.Canonical.ZornMatrix.dot X.x X.y = 0)
    (hx0 : X.x 0 ≠ 0) :
    ∃ U V : InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ,
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine U V =
        phaseToPlucker6 (offDiagonalPhase X) := by
  apply phaseNull_has_pluckerLine_of_q0_ne_zero
  · simpa [offDiagonalPhase, chiralPairing] using hnull
  · exact hx0

theorem offDiagonalPhase_pluckerLine_of_kleinNull
    (X : CanonicalZorn)
    (hK : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) = 0)
    (hx0 : X.x 0 ≠ 0) :
    ∃ U V : InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ,
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine U V =
        phaseToPlucker6 (offDiagonalPhase X) := by
  apply offDiagonalPhase_pluckerLine_of_null X
  · exact (kleinNull_offDiagonalPhase_iff X).1 hK
  · exact hx0

theorem offDiagonalPhase_pluckerLine_of_circularKleinNull
    (X : CanonicalZorn)
    (hK : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) = 0)
    (hc1 : circularCoordinate (cartesianZornLinearEquiv.symm X) 1 ≠ 0) :
    ∃ U V : InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ,
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine U V =
        phaseToPlucker6 (offDiagonalPhase X) := by
  apply offDiagonalPhase_pluckerLine_of_kleinNull X hK
  intro hx
  apply hc1
  have hcoord : X.x 0 =
      circularCoordinate (cartesianZornLinearEquiv.symm X) 1 := by
    simpa using (offDiagonalPhase_circular_coordinates X 0).1
  rw [← hcoord, hx]

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

theorem detZ_null_iff_kleinNull_of_diagonal_product_zero
    (X : CanonicalZorn) (hdiag : X.a * X.b = 0) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (phaseToPlucker6 (offDiagonalPhase X)) = 0 := by
  rw [detZ_eq_diagonal_sub_kleinQ, hdiag]
  constructor <;> intro h <;> linarith

end InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection
