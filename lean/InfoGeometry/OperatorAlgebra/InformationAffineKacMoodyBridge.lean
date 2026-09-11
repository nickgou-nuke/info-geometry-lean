import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge

Witness-gated bridge between Souriau/Amari information geometry and affine
current central readouts.

This module does not claim that dual flatness automatically implies
Kac--Moody closure.  It only names the calibration point:

* Souriau covariance (or equivalently Hessian) gives a Fisher-information readout;
* a supplied affine current bridge has a central scalar channel
  (`AffineCurrentDatum.killingForm`);
* if those scalar channels are calibrated to agree, the affine central readout
  is exactly the information-geometric covariance channel.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge

open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration

/--
Carrier for the information-geometry/affine-current calibration.

`Finite` is the finite current algebra carrier used by the affine socket.
`Source` is the Souriau source tangent carrier.  The map `toSource`
selects the Souriau source variation associated to a finite current direction.
-/
@[rep_depth operator]
structure InformationAffineKacMoodyCarrier
    (State Source LieDual E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- Souriau moment/covariance generator. -/
  momentGenerator : MomentMapGeneratingPotential State Source LieDual

  /-- Lightcone Sugawara/affine socket. -/
  sugawaraBridge :
    Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag

  /-- Map from finite current directions to Souriau source variations. -/
  toSource : Finite → Source

  /-- Fisher-information metric readout on finite current directions. -/
  fisherMetric : Finite → Finite → ℝ

namespace InformationAffineKacMoodyCarrier

variable
    {State Source LieDual E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B :
  InformationAffineKacMoodyCarrier
    State Source LieDual E Finite Alg Bog Korth Asplit Nshear CartanDiag)

/-- Souriau Hessian readout pulled back to finite current directions. -/
@[rep_depth operator]
def souriauHessianReadout (X Y : Finite) : ℝ :=
  B.momentGenerator.hessian (B.toSource X) (B.toSource Y)

/--
External predicate: the Fisher metric is the Souriau Hessian pulled back along
`toSource`.
-/
@[rep_depth operator]
def IsFisherMetricFromSouriauHessian : Prop :=
  ∀ X Y : Finite,
    B.fisherMetric X Y = B.souriauHessianReadout X Y

/--
External predicate: the Fisher metric is the Souriau covariance tensor pulled
back along `toSource`.
-/
@[rep_depth operator]
def IsFisherMetricFromSouriauCovariance : Prop :=
  ∀ X Y : Finite,
    B.fisherMetric X Y =
      B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y)

/--
External predicate: the affine central scalar channel is calibrated by the
Fisher metric.
-/
@[rep_depth operator]
def IsAffineCentralReadoutCalibratedByFisher : Prop :=
  ∀ X Y : Finite,
    B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      B.fisherMetric X Y

/-- Souriau Hessian equals covariance, pulled back to finite current directions. -/
@[rep_depth operator]
theorem souriauHessianReadout_eq_covarianceTensor
    (X Y : Finite) :
    B.souriauHessianReadout X Y =
      B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) := by
  unfold souriauHessianReadout
  exact B.momentGenerator.secondVariation_eq_covariance (B.toSource X) (B.toSource Y)

/-- If Fisher is the Souriau Hessian, then Fisher is the covariance readout. -/
@[rep_depth operator]
theorem fisherMetric_eq_souriauCovariance_of_hessian
    (hF : B.IsFisherMetricFromSouriauHessian)
    (X Y : Finite) :
    B.fisherMetric X Y =
      B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) := by
  rw [hF X Y]
  exact B.souriauHessianReadout_eq_covarianceTensor X Y

/-- Direct readback for the covariance-calibrated Fisher metric. -/
@[rep_depth operator]
theorem fisherMetric_eq_souriauCovariance
    (hF : B.IsFisherMetricFromSouriauCovariance)
    (X Y : Finite) :
    B.fisherMetric X Y =
      B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) :=
  hF X Y

/--
Pure calibration readback: if the affine central scalar channel is Fisher, and
Fisher is the Souriau Hessian/covariance readout, then the affine central scalar
channel is exactly the Souriau covariance channel.
-/
@[rep_depth operator]
theorem affineCentralReadout_eq_souriauCovariance
    (hF : B.IsFisherMetricFromSouriauCovariance)
    (hC : B.IsAffineCentralReadoutCalibratedByFisher)
    (X Y : Finite) :
    B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) := by
  rw [hC X Y]
  exact B.fisherMetric_eq_souriauCovariance hF X Y

/--
Hessian-lane variant: a Hessian-calibrated Fisher metric also gives the same
Souriau covariance calibration by the owner theorem
`MomentMapGeneratingPotential.secondVariation_eq_covariance`.
-/
@[rep_depth operator]
theorem affineCentralReadout_eq_souriauCovariance_of_hessian
    (hF : B.IsFisherMetricFromSouriauHessian)
    (hC : B.IsAffineCentralReadoutCalibratedByFisher)
    (X Y : Finite) :
    B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) := by
  rw [hC X Y]
  exact B.fisherMetric_eq_souriauCovariance_of_hessian hF X Y

/--
Under the same calibration, the affine central scalar appearing in the current
bracket is the covariance readout multiplied by the mode number.
-/
@[rep_depth operator]
theorem affineCentralCoefficient_eq_mode_mul_souriauCovariance
    (hF : B.IsFisherMetricFromSouriauCovariance)
    (hC : B.IsAffineCentralReadoutCalibratedByFisher)
    (m : ℤ) (X Y : Finite) :
    (m : ℝ) * B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      (m : ℝ) * B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) := by
  rw [B.affineCentralReadout_eq_souriauCovariance hF hC X Y]

/-- Hessian-lane variant of the affine central coefficient readback. -/
@[rep_depth operator]
theorem affineCentralCoefficient_eq_mode_mul_souriauCovariance_of_hessian
    (hF : B.IsFisherMetricFromSouriauHessian)
    (hC : B.IsAffineCentralReadoutCalibratedByFisher)
    (m : ℤ) (X Y : Finite) :
    (m : ℝ) * B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      (m : ℝ) * B.momentGenerator.covarianceTensor (B.toSource X) (B.toSource Y) := by
  rw [B.affineCentralReadout_eq_souriauCovariance_of_hessian hF hC X Y]

end InformationAffineKacMoodyCarrier

end InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge
