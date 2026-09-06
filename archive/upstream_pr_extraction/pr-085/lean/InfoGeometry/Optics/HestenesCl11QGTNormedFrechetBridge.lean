import InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge
import InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

set_option autoImplicit false

/-!
# Normed Fréchet realization of Hestenes-valued QGT curvature

This module packages the Hestenes split-quaternion QGT connection and maps its
curvature through the existing faithful finite-dimensional continuous
representation.  The maintained Chern character and its native Mathlib
Fréchet derivative are then specialized to this curvature.
-/

noncomputable section

namespace InfoGeometry.Optics.HestenesCl11QGTNormedFrechetBridge

open InfoGeometry.Canonical.Cl11CoordinateHestenesBridge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

/-- The original Hestenes-valued BKM/Berry QGT connection. -/
def hestenesQGTConnection {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    Connection (Point := Point) (Tangent := Tangent)
      (Value := DiracDoubledEnd) :=
  solderedQGTConnection
    (diracQGTField
      (hestenesCoordinateField colour symmetric)
      (hestenesCoordinateField colour antisymmetric))
    dQ dQ_swap dQ_same

/-- The connection obtained by Clifford-conjugating both Hestenes channels
and the exterior-derivative two-form. -/
def conjugateHestenesQGTConnection {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    Connection (Point := Point) (Tangent := Tangent)
      (Value := DiracDoubledEnd) :=
  solderedQGTConnection
    (diracQGTField
      (hestenesCoordinateField colour
        (hestenesConjugateField symmetric))
      (hestenesCoordinateField colour
        (hestenesConjugateField antisymmetric)))
    (conjugateDiracTwoForm dQ)
    (conjugateDiracTwoForm_swap dQ dQ_swap)
    (conjugateDiracTwoForm_same dQ dQ_same)

/-- The two packaged connections are related by the exact internal Dirac
frame transformation. -/
theorem conjugateHestenesQGTConnection_eq_internalFrame
    {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    conjugateHestenesQGTConnection colour symmetric antisymmetric
        dQ dQ_swap dQ_same =
      internalFrameConnection scalarPositiveComplexGammaUnit
        (hestenesQGTConnection colour symmetric antisymmetric
          dQ dQ_swap dQ_same) := by
  exact hestenesSolderedQGTConnection_covariant colour symmetric antisymmetric
    dQ dQ_swap dQ_same

/-- Faithful continuous-coordinate curvature of the Hestenes QGT
connection. -/
def hestenesCoordinateCurvature {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) : CoordinateContinuousEnd :=
  coordinateContinuousRepresentation
    (curvature
      (hestenesQGTConnection colour symmetric antisymmetric
        dQ dQ_swap dQ_same) p X Y)

/-- The named continuous Hestenes curvature is exactly the curvature obtained
after mapping the complete connection into the normed coordinate algebra. -/
theorem coordinateContinuousConnection_hestenes_curvature
    {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (coordinateContinuousConnection
          (hestenesQGTConnection colour symmetric antisymmetric
            dQ dQ_swap dQ_same)) p X Y =
      hestenesCoordinateCurvature colour symmetric antisymmetric
        dQ dQ_swap dQ_same p X Y := by
  exact coordinateContinuousConnection_curvature _ p X Y

/-- Faithful continuous-coordinate curvature after Hestenes Clifford
conjugation. -/
def conjugateHestenesCoordinateCurvature {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) : CoordinateContinuousEnd :=
  coordinateContinuousRepresentation
    (curvature
      (conjugateHestenesQGTConnection colour symmetric antisymmetric
        dQ dQ_swap dQ_same) p X Y)

/-- Hestenes Clifford conjugation becomes inner conjugation in the faithful
normed coordinate algebra. -/
theorem conjugateHestenesCoordinateCurvature_eq_innerConjugation
    {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    conjugateHestenesCoordinateCurvature colour symmetric antisymmetric
        dQ dQ_swap dQ_same p X Y =
      innerConjugation
        (coordinateContinuousUnit
          (doubledInternalUnit scalarPositiveComplexGammaUnit))
        (hestenesCoordinateCurvature colour symmetric antisymmetric
          dQ dQ_swap dQ_same p X Y) := by
  unfold conjugateHestenesCoordinateCurvature hestenesCoordinateCurvature
  rw [conjugateHestenesQGTConnection_eq_internalFrame,
    internalFrameConnection_curvature,
    coordinateContinuousRepresentation_innerConjugation]

/-- Every analytic coordinate Chern character is invariant under Hestenes
Clifford conjugation of the complete QGT curvature. -/
theorem coordinateFrechetChernCharacter_hestenesConjugation
    {Point Tangent : Type*}
    (k : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    coordinateFrechetChernCharacter k
        (conjugateHestenesCoordinateCurvature colour symmetric antisymmetric
          dQ dQ_swap dQ_same p X Y) =
      coordinateFrechetChernCharacter k
        (hestenesCoordinateCurvature colour symmetric antisymmetric
          dQ dQ_swap dQ_same p X Y) := by
  rw [conjugateHestenesCoordinateCurvature_eq_innerConjugation]
  exact coordinateFrechetChernCharacter_innerConjugation _ _ _

/-- Native Mathlib Fréchet differentiability at every represented Hestenes
QGT curvature. -/
theorem hasFDerivAt_coordinateFrechetChernCharacter_hestenesCurvature
    {Point Tangent : Type*}
    (k : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    HasFDerivAt (coordinateFrechetChernCharacter k)
      (coordinateFrechetChernCharacterDerivative k
        (hestenesCoordinateCurvature colour symmetric antisymmetric
          dQ dQ_swap dQ_same p X Y))
      (hestenesCoordinateCurvature colour symmetric antisymmetric
        dQ dQ_swap dQ_same p X Y) :=
  hasFDerivAt_coordinateFrechetChernCharacter _ _

/-- The Fréchet differential is covariant when both its Hestenes curvature
base point and tangent operator are Clifford-conjugated. -/
theorem fderiv_coordinateFrechetChernCharacter_hestenesConjugation
    {Point Tangent : Type*}
    (k : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) (H : CoordinateContinuousEnd) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (conjugateHestenesCoordinateCurvature colour symmetric antisymmetric
        dQ dQ_swap dQ_same p X Y))
        (innerConjugation
          (coordinateContinuousUnit
            (doubledInternalUnit scalarPositiveComplexGammaUnit)) H) =
      (fderiv ℂ (coordinateFrechetChernCharacter k)
        (hestenesCoordinateCurvature colour symmetric antisymmetric
          dQ dQ_swap dQ_same p X Y)) H := by
  rw [conjugateHestenesCoordinateCurvature_eq_innerConjugation]
  exact fderiv_coordinateFrechetChernCharacter_innerConjugation _ _ _ _

/-- Infinitesimal positive-Clifford transport of a Hestenes QGT curvature is
annihilated by every analytic Chern-character differential. -/
theorem fderiv_coordinateFrechetChernCharacter_hestenesCommutator
    {Point Tangent : Type*}
    (k : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (hestenesCoordinateCurvature colour symmetric antisymmetric
        dQ dQ_swap dQ_same p X Y))
      (associativeCommutator coordinateScalarPositiveGenerator
        (hestenesCoordinateCurvature colour symmetric antisymmetric
          dQ dQ_swap dQ_same p X Y)) = 0 := by
  exact fderiv_coordinateFrechetChernCharacter_associativeCommutator _ _ _

end InfoGeometry.Optics.HestenesCl11QGTNormedFrechetBridge
