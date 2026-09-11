import InfoGeometry.Twistor.PhaseNativePluckerBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

def plucker6ToPhase
    (P : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) : Phase :=
  (![P.p01, P.p02, P.p03], ![P.p23, -P.p13, P.p12])

noncomputable def phasePluckerEquiv :
    Phase ≃ InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ where
  toFun := phaseToPlucker6
  invFun := plucker6ToPhase
  left_inv X := by
    rcases X with ⟨x, y⟩
    ext i <;> fin_cases i <;> simp [phaseToPlucker6, plucker6ToPhase]
  right_inv P := by
    ext <;> simp [phaseToPlucker6, plucker6ToPhase]

@[simp] theorem phasePluckerEquiv_apply (X : Phase) :
    phasePluckerEquiv X = phaseToPlucker6 X := rfl

@[simp] theorem phasePluckerEquiv_symm_apply
    (P : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    phasePluckerEquiv.symm P = plucker6ToPhase P := rfl

theorem phaseToPlucker6_add (X Y : Phase) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add
        (phaseToPlucker6 X) (phaseToPlucker6 Y) =
      phaseToPlucker6 (X + Y) := by
  ext <;> simp [phaseToPlucker6,
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add]
  all_goals ring

theorem phaseToPlucker6_scale (r : ℝ) (X : Phase) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale r
        (phaseToPlucker6 X) =
      phaseToPlucker6 (r • X) := by
  ext <;> simp [phaseToPlucker6,
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale]

theorem plucker6_add_comm (P Q :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add P Q =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add Q P := by
  ext <;> simp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add] <;> ring

theorem plucker6_add_assoc (P Q R :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add P Q) R =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add P
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add Q R) := by
  ext <;> simp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add] <;> ring

theorem plucker6_scale_add (r : ℝ)
    (P Q : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale r
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add P Q) =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale r P)
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale r Q) := by
  ext <;> simp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.add,
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale] <;> ring

theorem plucker6_scale_scale (r s : ℝ)
    (P : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale r
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale s P) =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale (r * s) P := by
  ext <;> simp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale]
    <;> ring

theorem plucker6_scale_one
    (P : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale 1 P = P := by
  ext <;> simp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.scale]

theorem phaseNull_iff_phasePluckerEquiv_kleinNull (X : Phase) :
    chiralPairing X.1 X.2 = 0 ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phasePluckerEquiv X) = 0 := by
  simpa only [phasePluckerEquiv_apply] using
    (phaseNull_iff_kleinNull X)

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

theorem kleinQ_offDiagonalPhase_circular (X : CanonicalZorn) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) =
      circularCoordinate (cartesianZornLinearEquiv.symm X) 1 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 5 +
        circularCoordinate (cartesianZornLinearEquiv.symm X) 2 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 6 +
        circularCoordinate (cartesianZornLinearEquiv.symm X) 3 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 7 := by
  rw [phaseToPlucker6_offDiagonalPhase_circular]
  simp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ]

theorem kleinNull_offDiagonalPhase_circular_iff (X : CanonicalZorn) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 (offDiagonalPhase X)) = 0 ↔
      circularCoordinate (cartesianZornLinearEquiv.symm X) 1 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 5 +
        circularCoordinate (cartesianZornLinearEquiv.symm X) 2 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 6 +
        circularCoordinate (cartesianZornLinearEquiv.symm X) 3 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 7 = 0 := by
  rw [kleinQ_offDiagonalPhase_circular]

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
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X =
      X.a * X.b -
        InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (phaseToPlucker6 (offDiagonalPhase X)) := by
  rw [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    kleinQ_offDiagonalPhase]
  rfl

theorem detZ_eq_zero_iff_diagonal_eq_kleinQ (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X = 0 ↔
      X.a * X.b =
        InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (phaseToPlucker6 (offDiagonalPhase X)) := by
  rw [detZ_eq_diagonal_sub_kleinQ]
  exact sub_eq_zero

theorem detZ_null_iff_kleinNull_of_diagonal_product_zero
    (X : CanonicalZorn) (hdiag : X.a * X.b = 0) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X = 0 ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (phaseToPlucker6 (offDiagonalPhase X)) = 0 := by
  rw [detZ_eq_diagonal_sub_kleinQ, hdiag]
  constructor <;> intro h <;> linarith

end InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection
