import InfoGeometry.Physics.FreeEntropySouriauBridge
import Mathlib.Tactic.Linarith

/-!
# Free-entropy calibration and variation packet

This file is a small owner surface for the variation/calibration layer after the
Souriau/free-entropy bridge.

It bundles four scalar readouts that must remain conceptually separate:

* the value of `S_free`;
* the first variation of `S_free`;
* the effective stress tensor readout and the corresponding scalar Einstein
  residual;
* the boundary calibration residual for `S_BH = A / (4G)`.

The boundary statement is deliberately a calibration theorem.  It does not claim
that the Bekenstein-Hawking area law has been induced from the bulk action.
-/

namespace FreeEntropyCalibrationVariationPacket

noncomputable section

/--
Scalar packet carrying the free-entropy variation data, effective stress
readout data, and boundary calibration data.

The fields are explicit readouts rather than hidden assumptions.  Vanishing of
the residuals below is what imposes stationarity and boundary calibration.
-/
structure CalibrationVariationPacket where
  /-- Massieu-Planck contribution to `S_free`. -/
  massieu : ℝ
  /-- KL/Bregman informational deviation contribution. -/
  kl : ℝ
  /-- Incidence/null-flag friction contribution. -/
  incidenceFriction : ℝ
  /-- Free-probability energy contribution. -/
  freeEnergy : ℝ
  /-- Coupling for the incidence/null-flag contribution. -/
  lambdaInc : ℝ
  /-- Coupling for the free-probability contribution. -/
  lambdaFree : ℝ
  /-- First variation of the Massieu contribution. -/
  dMassieu : ℝ
  /-- First variation of the KL/Bregman contribution. -/
  dKL : ℝ
  /-- First variation of the incidence/null-flag friction contribution. -/
  dIncidenceFriction : ℝ
  /-- First variation of the free-probability energy contribution. -/
  dFreeEnergy : ℝ
  /-- Incidence/null-flag stress readout. -/
  incidenceStress : ℝ
  /-- Wick/Schwinger anomaly stress readout. -/
  anomalyStress : ℝ
  /-- Free-probability stress readout. -/
  freeStress : ℝ
  /-- Souriau/Massieu stress readout. -/
  souriauStress : ℝ
  /-- Scalar Einstein tensor readout. -/
  einsteinTensor : ℝ
  /-- Newton coupling readout. -/
  newtonG : ℝ
  /-- Boundary entropy readout. -/
  boundaryEntropy : ℝ
  /-- Boundary area readout. -/
  boundaryArea : ℝ
  /-- Boundary Newton coupling used for the area calibration. -/
  boundaryNewtonG : ℝ

/-- Value of the explicit `S_free` functional attached to the packet. -/
def S_free (P : CalibrationVariationPacket) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.S_free
    P.massieu P.kl P.incidenceFriction P.freeEnergy P.lambdaInc P.lambdaFree

/-- Expansion of the packet `S_free` value. -/
theorem S_free_eq (P : CalibrationVariationPacket) :
    S_free P =
      P.massieu - P.kl - P.lambdaInc * P.incidenceFriction -
        P.lambdaFree * P.freeEnergy := by
  rfl

/-- First variation of the packet `S_free` functional. -/
def S_freeFirstVariation (P : CalibrationVariationPacket) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.S_freeFirstVariation
    P.dMassieu P.dKL P.dIncidenceFriction P.dFreeEnergy P.lambdaInc P.lambdaFree

/-- Expansion of the packet first variation. -/
theorem S_freeFirstVariation_eq (P : CalibrationVariationPacket) :
    S_freeFirstVariation P =
      P.dMassieu - P.dKL - P.lambdaInc * P.dIncidenceFriction -
        P.lambdaFree * P.dFreeEnergy := by
  rfl

/-- `S_free` stationarity is exactly vanishing of the explicit first variation. -/
theorem S_free_stationary_iff (P : CalibrationVariationPacket) :
    S_freeFirstVariation P = 0 ↔
      P.dMassieu - P.dKL - P.lambdaInc * P.dIncidenceFriction -
        P.lambdaFree * P.dFreeEnergy = 0 := by
  rw [S_freeFirstVariation_eq]

/-- Effective stress readout of the incidence, anomaly, free, and Souriau layers. -/
def effectiveStressReadout (P : CalibrationVariationPacket) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.effectiveStressTensorReadout
    P.incidenceStress P.anomalyStress P.freeStress P.souriauStress

/-- Expansion of the effective stress readout. -/
theorem effectiveStressReadout_eq (P : CalibrationVariationPacket) :
    effectiveStressReadout P =
      P.incidenceStress + P.anomalyStress + P.freeStress + P.souriauStress := by
  rfl

/-- Scalar Einstein residual using the effective stress readout. -/
def effectiveEinsteinResidual (P : CalibrationVariationPacket) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.effectiveEinsteinResidual
    P.einsteinTensor P.newtonG P.incidenceStress P.anomalyStress P.freeStress
    P.souriauStress

/-- Zero residual is exactly the scalar effective Einstein balance. -/
theorem effectiveEinsteinResidual_eq_zero_iff (P : CalibrationVariationPacket) :
    effectiveEinsteinResidual P = 0 ↔
      P.einsteinTensor =
        (8 * Real.pi * P.newtonG) * effectiveStressReadout P := by
  unfold effectiveEinsteinResidual effectiveStressReadout
  exact InfoGeometry.Physics.FreeEntropySouriauBridge.effectiveEinsteinResidual_eq_zero_iff
    P.einsteinTensor P.newtonG P.incidenceStress P.anomalyStress P.freeStress
    P.souriauStress

/-- Boundary Hawking entropy readout `A / (4G)`. -/
def boundaryHawkingEntropy (area newtonG : ℝ) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.bekensteinHawkingEntropy area newtonG

/-- Boundary calibration residual for `S_BH = A / (4G)`. -/
def boundaryHawkingCalibrationResidual (P : CalibrationVariationPacket) : ℝ :=
  InfoGeometry.Physics.FreeEntropySouriauBridge.boundaryBHCalibrationResidual
    P.boundaryEntropy P.boundaryArea P.boundaryNewtonG

/--
The separate boundary calibration theorem: the residual vanishes exactly when
the boundary entropy readout matches `A / (4G)`.
-/
theorem boundaryHawkingCalibrationResidual_eq_zero_iff (P : CalibrationVariationPacket) :
    boundaryHawkingCalibrationResidual P = 0 ↔
      P.boundaryEntropy = boundaryHawkingEntropy P.boundaryArea P.boundaryNewtonG := by
  unfold boundaryHawkingCalibrationResidual boundaryHawkingEntropy
  exact InfoGeometry.Physics.FreeEntropySouriauBridge.boundaryBHCalibrationResidual_eq_zero_iff
    P.boundaryEntropy P.boundaryArea P.boundaryNewtonG

/-- The boundary calibration theorem written directly as `S_BH = A / (4G)`. -/
theorem boundaryHawkingCalibrationResidual_eq_zero_iff_area_over_fourG
    (P : CalibrationVariationPacket) :
    boundaryHawkingCalibrationResidual P = 0 ↔
      P.boundaryEntropy = P.boundaryArea / (4 * P.boundaryNewtonG) := by
  unfold boundaryHawkingCalibrationResidual
  unfold InfoGeometry.Physics.FreeEntropySouriauBridge.boundaryBHCalibrationResidual
  unfold InfoGeometry.Physics.FreeEntropySouriauBridge.bekensteinHawkingEntropy
  constructor
  · intro h
    linarith
  · intro h
    linarith

/--
The complete scalar calibration/stationarity condition for this packet:
free-entropy stationarity, effective Einstein balance, and boundary Hawking
calibration.
-/
def calibratedStationary (P : CalibrationVariationPacket) : Prop :=
  S_freeFirstVariation P = 0 ∧
    effectiveEinsteinResidual P = 0 ∧
      boundaryHawkingCalibrationResidual P = 0

/-- Expands the complete scalar calibration/stationarity condition. -/
theorem calibratedStationary_iff (P : CalibrationVariationPacket) :
    calibratedStationary P ↔
      (P.dMassieu - P.dKL - P.lambdaInc * P.dIncidenceFriction -
          P.lambdaFree * P.dFreeEnergy = 0) ∧
        (P.einsteinTensor =
          (8 * Real.pi * P.newtonG) * effectiveStressReadout P) ∧
          (P.boundaryEntropy = P.boundaryArea / (4 * P.boundaryNewtonG)) := by
  unfold calibratedStationary
  rw [S_free_stationary_iff]
  rw [effectiveEinsteinResidual_eq_zero_iff]
  rw [boundaryHawkingCalibrationResidual_eq_zero_iff_area_over_fourG]

end

end FreeEntropyCalibrationVariationPacket
