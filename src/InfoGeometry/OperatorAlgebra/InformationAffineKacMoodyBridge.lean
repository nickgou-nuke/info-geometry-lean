/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration
import InfoGeometry.Meta.Architecture

/-!
# Souriau Covariance and Affine Kac–Moody Central Channel Calibration

This module proves that pulling back the Souriau Hessian of a
`MomentMapGeneratingPotential` along a source map `toSource : Finite → Source`
yields the Souriau covariance tensor on `Finite`, and that whenever a Fisher
metric and an affine Kac–Moody Killing form are calibrated to that pullback,
the affine central coefficient `(m : ℝ) * killingForm X Y` equals the
mode-weighted Souriau covariance `(m : ℝ) * covarianceTensor (toSource X) (toSource Y)`.

- BUCKET 1 (Real Math in This File):
  - `souriauHessianReadout`, `souriauHessianReadout_eq_covarianceTensor`
  - `fisherMetric_eq_souriauCovariance_of_hessian`,
    `affineCentralReadout_eq_souriauCovariance`,
    `affineCentralReadout_eq_souriauCovariance_of_hessian`,
    `affineCentralCoefficient_eq_mode_mul_souriauCovariance`,
    `affineCentralCoefficient_eq_mode_mul_souriauCovariance_of_hessian`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential`
    (`MomentMapGeneratingPotential.secondVariation_eq_covariance`)
  - `InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge

open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration

variable
    {State Source LieDual E Finite Alg Bog Korth Asplit Nshear CartanDiag : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

/-- Souriau Hessian readout pulled back to finite current directions along `toSource`. -/
@[rep_depth operator]
def souriauHessianReadout
    (M : MomentMapGeneratingPotential State Source LieDual)
    (toSource : Finite → Source) (X Y : Finite) : ℝ :=
  M.hessian (toSource X) (toSource Y)

/-- Souriau Hessian equals covariance, pulled back to finite current directions. -/
@[rep_depth operator]
theorem souriauHessianReadout_eq_covarianceTensor
    (M : MomentMapGeneratingPotential State Source LieDual)
    (toSource : Finite → Source) (X Y : Finite) :
    souriauHessianReadout M toSource X Y =
      M.covarianceTensor (toSource X) (toSource Y) := by
  unfold souriauHessianReadout
  exact M.secondVariation_eq_covariance (toSource X) (toSource Y)

/-- If a Fisher metric equals the Souriau Hessian pullback, then it equals the
Souriau covariance pullback. -/
@[rep_depth operator]
theorem fisherMetric_eq_souriauCovariance_of_hessian
    (M : MomentMapGeneratingPotential State Source LieDual)
    (toSource : Finite → Source)
    (fisherMetric : Finite → Finite → ℝ)
    (hF : ∀ X Y : Finite, fisherMetric X Y = souriauHessianReadout M toSource X Y)
    (X Y : Finite) :
    fisherMetric X Y =
      M.covarianceTensor (toSource X) (toSource Y) := by
  rw [hF X Y]
  exact souriauHessianReadout_eq_covarianceTensor M toSource X Y

/-- If the affine central scalar channel is calibrated by `fisherMetric` and
`fisherMetric` is calibrated by the Souriau covariance pullback, then the
affine central scalar channel equals the Souriau covariance channel. -/
@[rep_depth operator]
theorem affineCentralReadout_eq_souriauCovariance
    (M : MomentMapGeneratingPotential State Source LieDual)
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (toSource : Finite → Source)
    (fisherMetric : Finite → Finite → ℝ)
    (hF : ∀ X Y : Finite,
      fisherMetric X Y = M.covarianceTensor (toSource X) (toSource Y))
    (hC : ∀ X Y : Finite,
      S.kanAffine.affineLightCone.affine.killingForm X Y = fisherMetric X Y)
    (X Y : Finite) :
    S.kanAffine.affineLightCone.affine.killingForm X Y =
      M.covarianceTensor (toSource X) (toSource Y) := by
  rw [hC X Y]
  exact hF X Y

/-- Hessian-lane variant: a Hessian-calibrated Fisher metric yields the same
Souriau covariance calibration for the affine Killing form. -/
@[rep_depth operator]
theorem affineCentralReadout_eq_souriauCovariance_of_hessian
    (M : MomentMapGeneratingPotential State Source LieDual)
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (toSource : Finite → Source)
    (fisherMetric : Finite → Finite → ℝ)
    (hF : ∀ X Y : Finite, fisherMetric X Y = souriauHessianReadout M toSource X Y)
    (hC : ∀ X Y : Finite,
      S.kanAffine.affineLightCone.affine.killingForm X Y = fisherMetric X Y)
    (X Y : Finite) :
    S.kanAffine.affineLightCone.affine.killingForm X Y =
      M.covarianceTensor (toSource X) (toSource Y) := by
  rw [hC X Y]
  exact fisherMetric_eq_souriauCovariance_of_hessian M toSource fisherMetric hF X Y

/-- Under covariance calibration, the mode-weighted affine central scalar
`(m : ℝ) * killingForm X Y` equals `(m : ℝ) * covarianceTensor (toSource X) (toSource Y)`. -/
@[rep_depth operator]
theorem affineCentralCoefficient_eq_mode_mul_souriauCovariance
    (M : MomentMapGeneratingPotential State Source LieDual)
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (toSource : Finite → Source)
    (fisherMetric : Finite → Finite → ℝ)
    (hF : ∀ X Y : Finite,
      fisherMetric X Y = M.covarianceTensor (toSource X) (toSource Y))
    (hC : ∀ X Y : Finite,
      S.kanAffine.affineLightCone.affine.killingForm X Y = fisherMetric X Y)
    (m : ℤ) (X Y : Finite) :
    (m : ℝ) * S.kanAffine.affineLightCone.affine.killingForm X Y =
      (m : ℝ) * M.covarianceTensor (toSource X) (toSource Y) := by
  rw [affineCentralReadout_eq_souriauCovariance M S toSource fisherMetric hF hC X Y]

/-- Hessian-lane variant of the mode-weighted affine central coefficient identity. -/
@[rep_depth operator]
theorem affineCentralCoefficient_eq_mode_mul_souriauCovariance_of_hessian
    (M : MomentMapGeneratingPotential State Source LieDual)
    (S : Calibration E Finite Alg Bog Korth Asplit Nshear CartanDiag)
    (toSource : Finite → Source)
    (fisherMetric : Finite → Finite → ℝ)
    (hF : ∀ X Y : Finite, fisherMetric X Y = souriauHessianReadout M toSource X Y)
    (hC : ∀ X Y : Finite,
      S.kanAffine.affineLightCone.affine.killingForm X Y = fisherMetric X Y)
    (m : ℤ) (X Y : Finite) :
    (m : ℝ) * S.kanAffine.affineLightCone.affine.killingForm X Y =
      (m : ℝ) * M.covarianceTensor (toSource X) (toSource Y) := by
  rw [affineCentralReadout_eq_souriauCovariance_of_hessian M S toSource fisherMetric hF hC X Y]

end InfoGeometry.OperatorAlgebra.InformationAffineKacMoodyBridge
