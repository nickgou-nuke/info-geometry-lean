import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge

Witness-gated bridge between Souriau/Amari information geometry and affine
current central readouts.

This module does not claim that dual flatness automatically implies
Kac--Moody closure.  It only names the calibration point:

* the operatorial BKM covariance gives a Fisher-information readout;
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

`Finite` is the finite current algebra carrier used by the affine construction.
`Source` is the parameter carrier of the operatorial Souriau family.  The map
`toSource` selects the parameter associated to a finite current direction.
-/
@[rep_depth operator]
structure InformationAffineKacMoodyCarrier
    (Source Obs E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*)
    [AddMonoid Source]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] where
  /-- Souriau moment/covariance generator. -/
  momentGenerator : MomentGeneratingReadout Source Obs

  /-- Lightcone Sugawara/affine relation. -/
  sugawaraBridge :
    Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag

  /-- Map from finite current directions to Souriau source variations. -/
  toSource : Finite → Source

  /-- Fisher-information metric readout on finite current directions. -/
  fisherMetric : Finite → Finite → ℝ

namespace InformationAffineKacMoodyCarrier

variable
    {Source Obs E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [AddMonoid Source]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

variable (B :
  InformationAffineKacMoodyCarrier
    Source Obs E Finite Alg Bog Korth Asplit Nshear CartanDiag)

/-- BKM covariance readout pulled back to finite current directions. -/
@[rep_depth operator]
def souriauCovarianceReadout (X Y : Finite) : ℝ :=
  B.momentGenerator.bkmCovariance
    (B.toSource X) (B.momentGenerator.family.generator (B.toSource X))
    (B.momentGenerator.family.generator (B.toSource Y))

/--
External predicate: the Fisher metric is the operatorial BKM covariance pulled
back along the native family generators and the parameter map, rather than a
scalar Hessian.
-/
@[rep_depth operator]
def IsFisherMetricFromSouriauCovariance : Prop :=
  ∀ X Y : Finite,
    B.fisherMetric X Y = B.souriauCovarianceReadout X Y

/--
External predicate: the affine central scalar channel is calibrated by the
Fisher metric.
-/
@[rep_depth operator]
def IsAffineCentralReadoutCalibratedByFisher : Prop :=
  ∀ X Y : Finite,
    B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      B.fisherMetric X Y

/-- Operatorial BKM covariance is the finite-current readout. -/
@[rep_depth operator]
theorem souriauCovarianceReadout_eq_bkmCovariance
    (X Y : Finite) :
      B.souriauCovarianceReadout X Y =
      B.momentGenerator.bkmCovariance
        (B.toSource X) (B.momentGenerator.family.generator (B.toSource X))
        (B.momentGenerator.family.generator (B.toSource Y)) := by
  rfl

/-- Direct readback for the covariance-calibrated Fisher metric. -/
@[rep_depth operator]
theorem fisherMetric_eq_souriauCovariance
    (hF : B.IsFisherMetricFromSouriauCovariance)
    (X Y : Finite) :
    B.fisherMetric X Y = B.souriauCovarianceReadout X Y :=
  hF X Y

/--
Pure calibration readback: if the affine central scalar channel is Fisher, and
Fisher is the operatorial BKM covariance readout, then the affine central
scalar channel is exactly that covariance channel.
-/
@[rep_depth operator]
theorem affineCentralReadout_eq_souriauCovariance
    (hF : B.IsFisherMetricFromSouriauCovariance)
    (hC : B.IsAffineCentralReadoutCalibratedByFisher)
    (X Y : Finite) :
    B.sugawaraBridge.kanAffine.affineLightCone.affine.killingForm X Y =
      B.souriauCovarianceReadout X Y := by
  rw [hC X Y]
  exact B.fisherMetric_eq_souriauCovariance hF X Y

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
      (m : ℝ) * B.souriauCovarianceReadout X Y := by
  rw [B.affineCentralReadout_eq_souriauCovariance hF hC X Y]


end InformationAffineKacMoodyCarrier

end InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge
