import InfoGeometry.Optics.HestenesCl11Cl44OperatorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance

set_option autoImplicit false

/-!
# Hestenes split-quaternion fields in the operator QGT curvature calculus

The existing QGT connection and curvature owners accept quaternionic `(4+4)`
coordinate fields.  This module supplies their canonical specialization to
Hestenes split-quaternion-valued BKM and Berry fields through one fixed-colour
associative split-octonion plane.  Curvature is reused unchanged.
-/

noncomputable section

namespace InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge

open InfoGeometry.Canonical.Cl11CoordinateHestenesBridge
open InfoGeometry.Canonical.HestenesDiracAdjoint
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Optics.HestenesCl11Cl44OperatorBridge
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Unified

/-- Solder each component of a Hestenes four-vector into one fixed-colour
associative plane of the quaternionic `(4+4)` carrier. -/
def hestenesCoordinateFourVector
    (colour : Fin 3) (v : Fin 4 → HestenesCl11) :
    Fin 4 → CartesianCoordinates :=
  fun μ => hestenesCartesian colour (v μ)

/-- Componentwise split-quaternion Clifford conjugation. -/
def hestenesConjugateFourVector
    (v : Fin 4 → HestenesCl11) : Fin 4 → HestenesCl11 :=
  fun μ => SplitQuaternion.cliffordConjugation (v μ)

/-- A QGT whose BKM and Berry channels are directly specified by Hestenes
split-quaternion four-vectors. -/
def hestenesDiracQGTFourVector
    (colour : Fin 3)
    (symmetric antisymmetric : Fin 4 → HestenesCl11) :
    QGTFourVector CanonicalZornCliffordRepresentation.DiracSpinor16 :=
  diracQGTFourVector
    (hestenesCoordinateFourVector colour symmetric)
    (hestenesCoordinateFourVector colour antisymmetric)

@[simp] theorem twistedConjCoordinates_hestenesCoordinateFourVector
    (colour : Fin 3) (v : Fin 4 → HestenesCl11) :
    twistedConjCoordinates (hestenesCoordinateFourVector colour v) =
      hestenesCoordinateFourVector colour (hestenesConjugateFourVector v) := by
  funext μ
  exact cartesianTwistedConj_hestenesCartesian colour (v μ)

/-- Internal complex Dirac conjugation is exactly componentwise Hestenes
Clifford conjugation on both QGT channels. -/
theorem qgtInternalConjugation_hestenesDiracQGTFourVector
    (colour : Fin 3)
    (symmetric antisymmetric : Fin 4 → HestenesCl11) :
    qgtInternalConjugation scalarPositiveComplexGammaUnit
        (hestenesDiracQGTFourVector colour symmetric antisymmetric) =
      hestenesDiracQGTFourVector colour
        (hestenesConjugateFourVector symmetric)
        (hestenesConjugateFourVector antisymmetric) := by
  unfold hestenesDiracQGTFourVector
  rw [qgtInternalConjugation_diracQGTFourVector,
    twistedConjCoordinates_hestenesCoordinateFourVector,
    twistedConjCoordinates_hestenesCoordinateFourVector]

/-- QGT soldering turns Hestenes Clifford conjugation into inner conjugation
on the doubled complex Dirac-spinor carrier. -/
theorem QGTSoldering_hestenesCliffordConjugation
    (colour : Fin 3)
    (symmetric antisymmetric : Fin 4 → HestenesCl11) :
    QGTSoldering
        (hestenesDiracQGTFourVector colour
          (hestenesConjugateFourVector symmetric)
          (hestenesConjugateFourVector antisymmetric)) =
      InfoGeometry.OperatorAlgebra.innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit)
        (QGTSoldering
          (hestenesDiracQGTFourVector colour symmetric antisymmetric)) := by
  rw [← qgtInternalConjugation_hestenesDiracQGTFourVector]
  exact QGTSoldering_internalConjugation scalarPositiveComplexGammaUnit _

/-- Pointwise/tangentwise soldering of a Hestenes-valued field. -/
def hestenesCoordinateField {Point Tangent : Type*}
    (colour : Fin 3)
    (v : Point → Tangent → Fin 4 → HestenesCl11) :
    Point → Tangent → Fin 4 → CartesianCoordinates :=
  fun p X => hestenesCoordinateFourVector colour (v p X)

/-- Componentwise Hestenes Clifford conjugation of a field. -/
def hestenesConjugateField {Point Tangent : Type*}
    (v : Point → Tangent → Fin 4 → HestenesCl11) :
    Point → Tangent → Fin 4 → HestenesCl11 :=
  fun p X => hestenesConjugateFourVector (v p X)

@[simp] theorem twistedConjCoordinateField_hestenesCoordinateField
    {Point Tangent : Type*}
    (colour : Fin 3)
    (v : Point → Tangent → Fin 4 → HestenesCl11) :
    twistedConjCoordinateField (hestenesCoordinateField colour v) =
      hestenesCoordinateField colour (hestenesConjugateField v) := by
  funext p X μ
  exact cartesianTwistedConj_hestenesCartesian colour (v p X μ)

/-- The complete Hestenes-conjugated QGT connection is the maintained
constant internal-frame transform of the original connection. -/
theorem hestenesSolderedQGTConnection_covariant
    {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    solderedQGTConnection
        (diracQGTField
          (hestenesCoordinateField colour
            (hestenesConjugateField symmetric))
          (hestenesCoordinateField colour
            (hestenesConjugateField antisymmetric)))
        (conjugateDiracTwoForm dQ)
        (conjugateDiracTwoForm_swap dQ dQ_swap)
        (conjugateDiracTwoForm_same dQ dQ_same) =
      internalFrameConnection scalarPositiveComplexGammaUnit
        (solderedQGTConnection
          (diracQGTField
            (hestenesCoordinateField colour symmetric)
            (hestenesCoordinateField colour antisymmetric))
          dQ dQ_swap dQ_same) := by
  rw [← twistedConjCoordinateField_hestenesCoordinateField,
    ← twistedConjCoordinateField_hestenesCoordinateField]
  exact solderedDiracQGTConnection_twistedConj_eq_internalFrame
    (hestenesCoordinateField colour symmetric)
    (hestenesCoordinateField colour antisymmetric)
    dQ dQ_swap dQ_same

/-- The full noncommutative QGT curvature is covariant under componentwise
Hestenes Clifford conjugation.  The exterior derivative two-form is the
existing conjugated two-form owner. -/
theorem hestenesSolderedQGTCurvature_covariant
    {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (solderedQGTConnection
          (diracQGTField
            (hestenesCoordinateField colour
              (hestenesConjugateField symmetric))
            (hestenesCoordinateField colour
              (hestenesConjugateField antisymmetric)))
          (conjugateDiracTwoForm dQ)
          (conjugateDiracTwoForm_swap dQ dQ_swap)
          (conjugateDiracTwoForm_same dQ dQ_same)) p X Y =
      InfoGeometry.OperatorAlgebra.innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit)
        (curvature
          (solderedQGTConnection
            (diracQGTField
              (hestenesCoordinateField colour symmetric)
              (hestenesCoordinateField colour antisymmetric))
            dQ dQ_swap dQ_same) p X Y) := by
  rw [← twistedConjCoordinateField_hestenesCoordinateField,
    ← twistedConjCoordinateField_hestenesCoordinateField]
  exact solderedDiracQGTConnection_twistedConj_curvature
    (hestenesCoordinateField colour symmetric)
    (hestenesCoordinateField colour antisymmetric)
    dQ dQ_swap dQ_same p X Y

/-- Every curvature power trace is invariant under Hestenes Clifford
conjugation of the BKM/Berry fields. -/
theorem hestenesSolderedQGTCurvature_tracePower
    {Point Tangent : Type*}
    (n : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    LinearMap.trace ℂ
        (Fin 2 → CanonicalZornCliffordRepresentation.DiracSpinor16)
        ((curvature
          (solderedQGTConnection
            (diracQGTField
              (hestenesCoordinateField colour
                (hestenesConjugateField symmetric))
              (hestenesCoordinateField colour
                (hestenesConjugateField antisymmetric)))
            (conjugateDiracTwoForm dQ)
            (conjugateDiracTwoForm_swap dQ dQ_swap)
            (conjugateDiracTwoForm_same dQ dQ_same)) p X Y) ^ n) =
      LinearMap.trace ℂ
        (Fin 2 → CanonicalZornCliffordRepresentation.DiracSpinor16)
        ((curvature
          (solderedQGTConnection
            (diracQGTField
              (hestenesCoordinateField colour symmetric)
              (hestenesCoordinateField colour antisymmetric))
            dQ dQ_swap dQ_same) p X Y) ^ n) := by
  rw [← twistedConjCoordinateField_hestenesCoordinateField,
    ← twistedConjCoordinateField_hestenesCoordinateField]
  exact solderedDiracQGTConnection_twistedConj_curvatureTracePower n
    (hestenesCoordinateField colour symmetric)
    (hestenesCoordinateField colour antisymmetric)
    dQ dQ_swap dQ_same p X Y

end InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge
