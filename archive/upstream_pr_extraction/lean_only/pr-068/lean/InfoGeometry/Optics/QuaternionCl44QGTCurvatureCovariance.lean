import InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance
import InfoGeometry.Optics.OperatorQGTConnectionCovariance
import InfoGeometry.Optics.OperatorQGTGaugeInvariants

set_option autoImplicit false

/-!
# Quaternionic `Cl(4,4)` covariance of the soldered QGT curvature

This file specializes the existing operator-connection covariance theorem to
the canonical complex Zorn Dirac carrier.  Both the BKM/Berry one-form and its
exterior-derivative two-form are transported by the positive scalar Clifford
implementer.  The resulting complete curvature is therefore exactly the
coordinatewise twisted-conjugate quaternionic curvature.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance

open CanonicalZornCliffordRepresentation
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorQGTGaugeInvariants
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance
open InfoGeometry.Unified

abbrev DiracDoubledEnd := Module.End ℂ (Fin 2 → DiracSpinor16)

/-- Gamma-valued QGT field obtained from two quaternionic `(4+4)` coordinate
fields, one for each symmetric/antisymmetric channel. -/
def diracQGTField {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates) :
    Point → Tangent → QGTFourVector DiracSpinor16 :=
  fun p X ↦ diracQGTFourVector (symmetric p X) (antisymmetric p X)

/-- Apply the transported split-quaternion conjugation at every point,
tangent direction, and operator coordinate. -/
def twistedConjCoordinateField {Point Tangent : Type*}
    (v : Point → Tangent → Fin 4 → CartesianCoordinates) :
    Point → Tangent → Fin 4 → CartesianCoordinates :=
  fun p X i ↦ cartesianTwistedConj (v p X i)

/-- Conjugate a doubled-spinor-valued exterior-derivative two-form by the
same internal Dirac frame used for its QGT one-form. -/
def conjugateDiracTwoForm {Point Tangent : Type*}
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd) :
    Point → Tangent → Tangent → DiracDoubledEnd :=
  fun p X Y ↦ innerConjugation
    (doubledInternalUnit scalarPositiveComplexGammaUnit) (dQ p X Y)

theorem conjugateDiracTwoForm_swap {Point Tangent : Type*}
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (p : Point) (X Y : Tangent) :
    conjugateDiracTwoForm dQ p Y X =
      -conjugateDiracTwoForm dQ p X Y := by
  rw [conjugateDiracTwoForm, dQ_swap]
  exact map_neg
    (innerConjugationRingEquiv
      (doubledInternalUnit scalarPositiveComplexGammaUnit)) (dQ p X Y)

theorem conjugateDiracTwoForm_same {Point Tangent : Type*}
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X : Tangent) :
    conjugateDiracTwoForm dQ p X X = 0 := by
  rw [conjugateDiracTwoForm, dQ_same]
  exact map_zero
    (innerConjugationRingEquiv
      (doubledInternalUnit scalarPositiveComplexGammaUnit))

/-- The coordinatewise twisted-conjugate QGT field is exactly internal
conjugation of the original gamma-valued QGT field. -/
theorem diracQGTField_twistedConj {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (p : Point) (X : Tangent) :
    diracQGTField
        (twistedConjCoordinateField symmetric)
        (twistedConjCoordinateField antisymmetric) p X =
      qgtInternalConjugation scalarPositiveComplexGammaUnit
        (diracQGTField symmetric antisymmetric p X) := by
  exact (qgtInternalConjugation_diracQGTFourVector
    (symmetric p X) (antisymmetric p X)).symm

/-- The full connection built from twisted quaternionic coordinates and the
conjugated exterior derivative is the canonical inner-frame transform of the
original soldered connection. -/
theorem solderedDiracQGTConnection_twistedConj_eq_internalFrame
    {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    solderedQGTConnection
        (diracQGTField
          (twistedConjCoordinateField symmetric)
          (twistedConjCoordinateField antisymmetric))
        (conjugateDiracTwoForm dQ)
        (conjugateDiracTwoForm_swap dQ dQ_swap)
        (conjugateDiracTwoForm_same dQ dQ_same) =
      internalFrameConnection scalarPositiveComplexGammaUnit
        (solderedQGTConnection
          (diracQGTField symmetric antisymmetric)
          dQ dQ_swap dQ_same) := by
  unfold solderedQGTConnection internalFrameConnection
    innerConjugateConnection mapConnection
  rw [Connection.mk.injEq]
  constructor
  · funext p X
    exact QGTSoldering_dirac_twistedConj_covariant
      (symmetric p X) (antisymmetric p X)
  · rfl

/-- Complete curvature covariance for the quaternionic Dirac-valued QGT
connection.  This includes both the conjugated exterior derivative and the
noncommutative wedge square of the soldered BKM/Berry one-form. -/
theorem solderedDiracQGTConnection_twistedConj_curvature
    {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (solderedQGTConnection
          (diracQGTField
            (twistedConjCoordinateField symmetric)
            (twistedConjCoordinateField antisymmetric))
          (conjugateDiracTwoForm dQ)
          (conjugateDiracTwoForm_swap dQ dQ_swap)
          (conjugateDiracTwoForm_same dQ dQ_same)) p X Y =
      innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit)
        (curvature
          (solderedQGTConnection
            (diracQGTField symmetric antisymmetric)
            dQ dQ_swap dQ_same) p X Y) := by
  rw [solderedDiracQGTConnection_twistedConj_eq_internalFrame]
  exact internalFrameConnection_curvature
    scalarPositiveComplexGammaUnit
    (solderedQGTConnection
      (diracQGTField symmetric antisymmetric)
      dQ dQ_swap dQ_same) p X Y

/-- Every native curvature power trace is unchanged by coordinatewise
split-quaternion twisted conjugation.  Thus the scalar Chern--Weil readouts
factor through the concrete quaternionic Dirac frame orbit. -/
theorem solderedDiracQGTConnection_twistedConj_curvatureTracePower
    {Point Tangent : Type*}
    (n : ℕ)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        ((curvature
          (solderedQGTConnection
            (diracQGTField
              (twistedConjCoordinateField symmetric)
              (twistedConjCoordinateField antisymmetric))
            (conjugateDiracTwoForm dQ)
            (conjugateDiracTwoForm_swap dQ dQ_swap)
            (conjugateDiracTwoForm_same dQ dQ_same)) p X Y) ^ n) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        ((curvature
          (solderedQGTConnection
            (diracQGTField symmetric antisymmetric)
            dQ dQ_swap dQ_same) p X Y) ^ n) := by
  rw [solderedDiracQGTConnection_twistedConj_curvature]
  exact trace_pow_innerConjugation
    (doubledInternalUnit scalarPositiveComplexGammaUnit)
    (curvature
      (solderedQGTConnection
        (diracQGTField symmetric antisymmetric)
        dQ dQ_swap dQ_same) p X Y) n

/-- Closure packet joining twisted quaternionic coordinates, the gamma-valued
QGT one-form, its two-operator exterior derivative, and full curvature. -/
theorem quaternion_cl44_qgt_curvature_covariance_packet
    {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    (∀ p X,
      diracQGTField
          (twistedConjCoordinateField symmetric)
          (twistedConjCoordinateField antisymmetric) p X =
        qgtInternalConjugation scalarPositiveComplexGammaUnit
          (diracQGTField symmetric antisymmetric p X)) ∧
    (∀ p X Y,
      curvature
          (solderedQGTConnection
            (diracQGTField
              (twistedConjCoordinateField symmetric)
              (twistedConjCoordinateField antisymmetric))
            (conjugateDiracTwoForm dQ)
            (conjugateDiracTwoForm_swap dQ dQ_swap)
            (conjugateDiracTwoForm_same dQ dQ_same)) p X Y =
        innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit)
          (curvature
            (solderedQGTConnection
              (diracQGTField symmetric antisymmetric)
              dQ dQ_swap dQ_same) p X Y)) := by
  exact ⟨diracQGTField_twistedConj symmetric antisymmetric,
    solderedDiracQGTConnection_twistedConj_curvature
      symmetric antisymmetric dQ dQ_swap dQ_same⟩

end InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance

end noncomputable section
