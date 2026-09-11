import InfoGeometry.Optics.FiniteBKMDiracCurvatureBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.FiniteBKMDiracFrechetBridge

open CanonicalZornCliffordRepresentation
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.FiniteBKMDiracCurvatureBridge
open InfoGeometry.Optics.FiniteBKMDiracTransport
open InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
open InfoGeometry.Unified
open SouriauOnsagerBKM

variable {Point Tangent E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine integrated BKM/Berry connection after exact transport to the
sixteen-component Zorn Dirac carrier. -/
def finiteBKMDiracConnection
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    Connection (Point := Point) (Tangent := Tangent)
      (Value := DiracDoubledEnd) :=
  solderedQGTConnection
    (diracBKMAndBerryField D observable berryOperator left right)
    (transportTwoForm finiteHilbertSixteenDiracEquiv dQ)
    (transportTwoForm_swap finiteHilbertSixteenDiracEquiv dQ dQ_swap)
    (transportTwoForm_same finiteHilbertSixteenDiracEquiv dQ dQ_same)

/-- Faithful normed-coordinate curvature of the genuine BKM/Berry Dirac
connection. -/
def finiteBKMDiracCoordinateCurvature
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) : CoordinateContinuousEnd :=
  coordinateContinuousRepresentation
    (curvature
      (finiteBKMDiracConnection D observable berryOperator left right
        dQ dQ_swap dQ_same) p X Y)

/-- Mapping the complete connection and then taking curvature produces the
named faithful BKM/Berry coordinate curvature. -/
theorem coordinateContinuousConnection_finiteBKMDirac_curvature
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (coordinateContinuousConnection
          (finiteBKMDiracConnection D observable berryOperator left right
            dQ dQ_swap dQ_same)) p X Y =
      finiteBKMDiracCoordinateCurvature D observable berryOperator left right
        dQ dQ_swap dQ_same p X Y := by
  exact coordinateContinuousConnection_curvature _ p X Y

/-- The analytic coordinate Chern character of genuine BKM/Berry curvature
equals the native algebraic trace on its original finite Hilbert carrier. -/
theorem coordinateFrechetChernCharacter_finiteBKMDirac_eq_finiteTrace
    (k : ℕ)
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    coordinateFrechetChernCharacter k
        (finiteBKMDiracCoordinateCurvature D observable berryOperator
          left right dQ dQ_swap dQ_same p X Y) =
      LinearMap.trace ℂ (Fin 2 → FiniteHilbertSpace 16)
        ((curvature
          (solderedQGTConnection
            (finiteBKMAndBerryField D observable berryOperator left right)
            dQ dQ_swap dQ_same) p X Y) ^ k) := by
  unfold coordinateFrechetChernCharacter
    finiteBKMDiracCoordinateCurvature
  rw [coordinateFrechetTracePower_representation]
  exact diracBKMAndBerry_curvature_tracePower
    k D observable berryOperator left right dQ dQ_swap dQ_same p X Y

/-- Native Mathlib Fréchet differentiability of every characteristic power
at the genuine BKM/Berry curvature. -/
theorem hasFDerivAt_coordinateFrechetChernCharacter_finiteBKMDirac
    (k : ℕ)
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    HasFDerivAt (coordinateFrechetChernCharacter k)
      (coordinateFrechetChernCharacterDerivative k
        (finiteBKMDiracCoordinateCurvature D observable berryOperator
          left right dQ dQ_swap dQ_same p X Y))
      (finiteBKMDiracCoordinateCurvature D observable berryOperator
        left right dQ dQ_swap dQ_same p X Y) :=
  hasFDerivAt_coordinateFrechetChernCharacter _ _

/-- Infinitesimal inner Bogoliubov directions of genuine BKM/Berry curvature
are killed by every analytic coordinate Chern-character differential. -/
theorem fderiv_coordinateFrechetChernCharacter_finiteBKMDirac_commutator
    (k : ℕ)
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) (Z : CoordinateContinuousEnd) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (finiteBKMDiracCoordinateCurvature D observable berryOperator
        left right dQ dQ_swap dQ_same p X Y))
      (associativeCommutator Z
        (finiteBKMDiracCoordinateCurvature D observable berryOperator
          left right dQ dQ_swap dQ_same p X Y)) = 0 := by
  exact fderiv_coordinateFrechetChernCharacter_associativeCommutator _ _ _

/-- A witnessed Hestenes realization remains exact after passing to the
faithful normed coordinate curvature. -/
theorem hestenesRealization_coordinateCurvature_eq_finiteBKM
    (colour : Fin 3)
    (symmetric antisymmetric : Point → Tangent → Fin 4 →
      InfoGeometry.Canonical.Cl11CoordinateHestenesBridge.HestenesCl11)
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (hQ : IsHestenesRealization colour symmetric antisymmetric
      (diracBKMAndBerryField D observable berryOperator left right))
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    coordinateContinuousRepresentation
        (curvature
          (solderedQGTConnection
            (diracQGTField
              (hestenesCoordinateField colour symmetric)
              (hestenesCoordinateField colour antisymmetric))
            (transportTwoForm finiteHilbertSixteenDiracEquiv dQ)
            (transportTwoForm_swap finiteHilbertSixteenDiracEquiv dQ dQ_swap)
            (transportTwoForm_same finiteHilbertSixteenDiracEquiv dQ dQ_same))
          p X Y) =
      coordinateContinuousRepresentation
        (transportDoubledEnd finiteHilbertSixteenDiracEquiv
          (curvature
            (solderedQGTConnection
              (finiteBKMAndBerryField D observable berryOperator left right)
              dQ dQ_swap dQ_same) p X Y)) := by
  exact congrArg coordinateContinuousRepresentation
    (hestenesRealization_curvature_eq_finiteBKMTransport
      colour symmetric antisymmetric D observable berryOperator left right hQ
      dQ dQ_swap dQ_same p X Y)

end InfoGeometry.Optics.FiniteBKMDiracFrechetBridge
