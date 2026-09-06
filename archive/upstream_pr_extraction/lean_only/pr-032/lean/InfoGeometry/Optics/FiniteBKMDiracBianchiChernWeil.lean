import InfoGeometry.Optics.FiniteBKMDiracFrechetBridge
import InfoGeometry.Optics.OperatorQGTChernWeil

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.FiniteBKMDiracBianchiChernWeil

open CanonicalZornCliffordRepresentation
open InfoGeometry.Optics.FiniteBKMDiracCurvatureBridge
open InfoGeometry.Optics.FiniteBKMDiracFrechetBridge
open InfoGeometry.Optics.FiniteBKMDiracTransport
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.OperatorQGTChernWeil
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
open SouriauOnsagerBKM

variable {Point Tangent E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The adjoint Bianchi identity gives algebraic Chern--Weil closedness for
the genuine BKM/Berry Dirac connection. -/
theorem trace_finiteBKMDirac_curvaturePowerDerivative_zero_of_bianchi
    (n : ℕ)
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
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (hBianchi : SatisfiesAdjointBianchi
      (finiteBKMDiracConnection D observable berryOperator left right
        dQ dQ_swap dQ_same) dF)
    (p : Point) (X U V : Tangent) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n
          (curvature
            (finiteBKMDiracConnection D observable berryOperator left right
              dQ dQ_swap dQ_same) p U V)
          (dF p X U V)) = 0 := by
  exact trace_curvaturePowerDerivative_zero_of_bianchi n
    (finiteBKMDiracConnection D observable berryOperator left right
      dQ dQ_swap dQ_same) dF hBianchi p X U V

/-- The faithful normed coordinate trace computes the same ordered
curvature-power differential as the algebraic Dirac trace. -/
theorem coordinateTrace_finiteBKMDirac_curvaturePowerDerivative
    (n : ℕ)
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
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (p : Point) (X U V : Tangent) :
    coordinateTraceCLM
        (operatorPowerDerivative n
          (finiteBKMDiracCoordinateCurvature D observable berryOperator
            left right dQ dQ_swap dQ_same p U V)
          (coordinateContinuousRepresentation (dF p X U V))) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n
          (curvature
            (finiteBKMDiracConnection D observable berryOperator left right
              dQ dQ_swap dQ_same) p U V)
          (dF p X U V)) := by
  exact coordinateTrace_operatorPowerDerivative_representation n _ _

/-- Full Chern--Weil closedness in the faithful normed coordinate
realization of the genuine BKM/Berry connection. -/
theorem coordinateTrace_finiteBKMDirac_curvaturePowerDerivative_zero_of_bianchi
    (n : ℕ)
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
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (hBianchi : SatisfiesAdjointBianchi
      (finiteBKMDiracConnection D observable berryOperator left right
        dQ dQ_swap dQ_same) dF)
    (p : Point) (X U V : Tangent) :
    coordinateTraceCLM
        (operatorPowerDerivative n
          (finiteBKMDiracCoordinateCurvature D observable berryOperator
            left right dQ dQ_swap dQ_same p U V)
          (coordinateContinuousRepresentation (dF p X U V))) = 0 := by
  rw [coordinateTrace_finiteBKMDirac_curvaturePowerDerivative]
  exact trace_finiteBKMDirac_curvaturePowerDerivative_zero_of_bianchi
    n D observable berryOperator left right dQ dQ_swap dQ_same dF hBianchi
    p X U V

end InfoGeometry.Optics.FiniteBKMDiracBianchiChernWeil
