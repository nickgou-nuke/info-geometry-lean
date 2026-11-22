/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CanonicalZornBraidTransport
import InfoGeometry.Canonical.OperatorZornGaugeCovariance

noncomputable section

namespace InfoGeometry.Canonical.OperatorZornBraidGaugeAction

open InfoGeometry.Physics.QCDCanonicalComplexZornBridge
open InfoGeometry.Canonical.CanonicalZornBraidTransport
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.Canonical.OperatorZornGaugeCovariance
open InfoGeometry.Canonical.OperatorZornRepresentationCurvatureBridge
open InfoGeometry.Physics.NCG
open InfoGeometry.Physics.B3PresentedGroup

abbrev CoefficientOperator :=
  Module.End ℂ InfoGeometry.Physics.QCDCanonicalComplexZornBridge.CanonicalZorn
abbrev OperatorField := OperatorZornMatrix CoefficientOperator
abbrev OperatorPotential := FourPotential CoefficientOperator

theorem coefficientConjugation_mul_apply (g h : CoefficientOperatorˣ)
    (x : CoefficientOperator) :
    coefficientConjugation (g * h) x =
      coefficientConjugation g (coefficientConjugation h x) := by
  change ((g * h : CoefficientOperatorˣ) : CoefficientOperator) * x *
      (((g * h)⁻¹ : CoefficientOperatorˣ) : CoefficientOperator) =
    (g : CoefficientOperator) *
      ((h : CoefficientOperator) * x * ((h⁻¹ : CoefficientOperatorˣ) : CoefficientOperator)) *
        ((g⁻¹ : CoefficientOperatorˣ) : CoefficientOperator)
  simp only [Units.val_mul, mul_inv]
  noncomm_ring

theorem gauge_one_apply (X : OperatorField) :
    gauge (1 : CoefficientOperatorˣ) X = X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [OperatorZornGaugeCovariance.gauge, mapCoefficients, mapOperatorVector,
    coefficientConjugation]

theorem gauge_mul_apply (g h : CoefficientOperatorˣ) (X : OperatorField) :
    gauge (g * h) X = gauge g (gauge h X) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [OperatorZornGaugeCovariance.gauge, mapCoefficients, mapOperatorVector,
    coefficientConjugation_mul_apply]

def braidGaugeAction (braid : B3) (X : OperatorField) : OperatorField :=
  OperatorZornGaugeCovariance.gauge (braidRepresentation braid) X

theorem braidGaugeAction_one (X : OperatorField) :
    braidGaugeAction 1 X = X := by
  rw [braidGaugeAction, map_one]
  exact gauge_one_apply X

theorem braidGaugeAction_mul (left right : B3) (X : OperatorField) :
    braidGaugeAction (left * right) X =
      braidGaugeAction left (braidGaugeAction right X) := by
  simpa [braidGaugeAction] using
    (gauge_mul_apply (braidRepresentation left) (braidRepresentation right) X)

theorem braidGaugeAction_fieldStrength (braid : B3)
    (p : Fin 4 → CoefficientOperator) (Phi : OperatorPotential) (mu nu : Fin 4) :
    braidGaugeAction braid (fieldStrength p Phi mu nu) =
      fieldStrength
        (fun i => coefficientConjugation (braidRepresentation braid) (p i))
        (fun i => braidGaugeAction braid (Phi i)) mu nu := by
  simpa [braidGaugeAction] using
    (gauge_fieldStrength (braidRepresentation braid) p Phi mu nu)

theorem braidGaugeAction_curvatureAction (braid : B3)
    (p : Fin 4 → CoefficientOperator) (Phi : OperatorPotential)
    (mu nu : Fin 4) (X : OperatorField) :
    braidGaugeAction braid (curvatureAction p Phi mu nu X) =
      curvatureAction
        (fun i => coefficientConjugation (braidRepresentation braid) (p i))
        (fun i => braidGaugeAction braid (Phi i)) mu nu (braidGaugeAction braid X) := by
  simpa [braidGaugeAction] using
    (gauge_curvatureAction (braidRepresentation braid) p Phi mu nu X)

theorem braidGaugeAction_bianchi (braid : B3)
    (p : Fin 4 → CoefficientOperator) (Phi : OperatorPotential)
    (mu nu rho : Fin 4) :
    braidGaugeAction braid (bianchi p Phi mu nu rho) =
      bianchi
        (fun i => coefficientConjugation (braidRepresentation braid) (p i))
        (fun i => braidGaugeAction braid (Phi i)) mu nu rho := by
  simpa [braidGaugeAction] using
    (gauge_bianchi (braidRepresentation braid) p Phi mu nu rho)

end InfoGeometry.Canonical.OperatorZornBraidGaugeAction
