import InfoGeometry.Optics.HestenesCl11QGTNormedFrechetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.QuaternionCl44QGTBianchiChernWeil

set_option autoImplicit false

/-!
# Hestenes QGT Bianchi and Chern--Weil closure

This module specializes the maintained adjoint Bianchi equation and ordered
noncommutative Chern--Weil derivative to the named Hestenes QGT connection.
It also identifies the algebraic trace with the trace in the faithful normed
coordinate realization.
-/

noncomputable section

namespace InfoGeometry.Optics.HestenesCl11QGTBianchiChernWeilBridge

open CanonicalZornCliffordRepresentation
open InfoGeometry.Canonical.Cl11CoordinateHestenesBridge
open InfoGeometry.Optics.HestenesCl11QGTNormedFrechetBridge
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.OperatorQGTChernWeil
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTBianchiChernWeil
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

/-- Hestenes Clifford conjugation preserves and reflects the complete
adjoint Bianchi equation. -/
theorem conjugateHestenesQGT_satisfiesAdjointBianchi_iff
    {Point Tangent : Type*}
    (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd) :
    SatisfiesAdjointBianchi
        (conjugateHestenesQGTConnection colour symmetric antisymmetric
          dQ dQ_swap dQ_same)
        (conjugateDiracCurvatureDifferential dF) ↔
      SatisfiesAdjointBianchi
        (hestenesQGTConnection colour symmetric antisymmetric
          dQ dQ_swap dQ_same) dF := by
  rw [conjugateHestenesQGTConnection_eq_internalFrame]
  exact internalFrame_satisfiesAdjointBianchi_iff
    (hestenesQGTConnection colour symmetric antisymmetric
      dQ dQ_swap dQ_same) dF

/-- Algebraic Chern--Weil closedness for every ordered curvature power of
the original Hestenes QGT connection. -/
theorem trace_hestenes_curvaturePowerDerivative_zero_of_bianchi
    {Point Tangent : Type*}
    (n : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (hBianchi : SatisfiesAdjointBianchi
      (hestenesQGTConnection colour symmetric antisymmetric
        dQ dQ_swap dQ_same) dF)
    (p : Point) (X U V : Tangent) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n
          (curvature
            (hestenesQGTConnection colour symmetric antisymmetric
              dQ dQ_swap dQ_same) p U V)
          (dF p X U V)) = 0 := by
  exact trace_curvaturePowerDerivative_zero_of_bianchi n
    (hestenesQGTConnection colour symmetric antisymmetric
      dQ dQ_swap dQ_same) dF hBianchi p X U V

/-- Chern--Weil closedness in the Clifford-conjugated Hestenes frame. -/
theorem trace_conjugateHestenes_curvaturePowerDerivative_zero_of_bianchi
    {Point Tangent : Type*}
    (n : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (hBianchi : SatisfiesAdjointBianchi
      (hestenesQGTConnection colour symmetric antisymmetric
        dQ dQ_swap dQ_same) dF)
    (p : Point) (X U V : Tangent) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n
          (curvature
            (conjugateHestenesQGTConnection colour symmetric antisymmetric
              dQ dQ_swap dQ_same) p U V)
          (conjugateDiracCurvatureDifferential dF p X U V)) = 0 := by
  apply trace_curvaturePowerDerivative_zero_of_bianchi n
  exact (conjugateHestenesQGT_satisfiesAdjointBianchi_iff colour
    symmetric antisymmetric dQ dQ_swap dQ_same dF).2 hBianchi

/-- The continuous-coordinate trace of the represented ordered Hestenes
curvature-power derivative is exactly its algebraic Chern--Weil trace. -/
theorem coordinateTrace_hestenes_curvaturePowerDerivative
    {Point Tangent : Type*}
    (n : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (p : Point) (X U V : Tangent) :
    coordinateTraceCLM
        (operatorPowerDerivative n
          (hestenesCoordinateCurvature colour symmetric antisymmetric
            dQ dQ_swap dQ_same p U V)
          (coordinateContinuousRepresentation (dF p X U V))) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n
          (curvature
            (hestenesQGTConnection colour symmetric antisymmetric
              dQ dQ_swap dQ_same) p U V)
          (dF p X U V)) := by
  exact coordinateTrace_operatorPowerDerivative_representation n _ _

/-- Normed-coordinate Chern--Weil closedness follows from the same adjoint
Bianchi equation, with no loss across the faithful representation. -/
theorem coordinateTrace_hestenes_curvaturePowerDerivative_zero_of_bianchi
    {Point Tangent : Type*}
    (n : ℕ) (colour : Fin 3)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → HestenesCl11)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (hBianchi : SatisfiesAdjointBianchi
      (hestenesQGTConnection colour symmetric antisymmetric
        dQ dQ_swap dQ_same) dF)
    (p : Point) (X U V : Tangent) :
    coordinateTraceCLM
        (operatorPowerDerivative n
          (hestenesCoordinateCurvature colour symmetric antisymmetric
            dQ dQ_swap dQ_same p U V)
          (coordinateContinuousRepresentation (dF p X U V))) = 0 := by
  rw [coordinateTrace_hestenes_curvaturePowerDerivative]
  exact trace_hestenes_curvaturePowerDerivative_zero_of_bianchi n colour
    symmetric antisymmetric dQ dQ_swap dQ_same dF hBianchi p X U V

end InfoGeometry.Optics.HestenesCl11QGTBianchiChernWeilBridge

