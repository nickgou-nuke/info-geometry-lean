import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.QuaternionEffectiveActionBridge
import InfoGeometry.Physics.FreeEntropyCalibrationVariationPacket

/-!
# InfoGeometry.Canonical.QuaternionCalibratedStationaryBridge

This is a theorem-safe finite bridge that combines:

* negative-log effective action readback;
* scalar calibrated-stationary packet (stationarity + effective Einstein balance
  + boundary Hawking calibration);
* quaternion field residual equivalence.

It does not derive path integrals, loop expansions, RG beta functions,
non-perturbative FRG equations, or black-hole evaporation corrections.
-/

noncomputable section

open InfoGeometry.Physics.FreeEntropyCalibrationVariationPacket

namespace InfoGeometry.Canonical.QuaternionCalibratedStationaryBridge

open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Canonical.QuaternionEffectiveActionBridge
open InfoGeometry.Canonical.QuaternionGeometry

section

variable {n : ℕ}
variable {SpaceTime : Type*} [Fintype SpaceTime]
variable {idx : Type*} [Fintype idx]
variable {Spinor : Type*} [AddCommGroup Spinor] [Module ℂ Spinor]
variable {Operator : Type*} [Ring Operator] [StarRing Operator] [Module ℂ Operator]
variable [StarModule ℂ Operator]

variable (nabla : SpaceTime → Spinor → Spinor)
variable (e_inv : SpaceTime → idx → ℝ)
variable (m : ℝ)
variable (gamma_action : idx → Spinor → Spinor)
variable (Q : Spinor)

/-- Honest finite compatibility packet for the current quaternion bridge lane. -/
def quaternionCalibratedStationary
    (D : NarainSupervolumeBridgeData n)
    (P : CalibrationVariationData) : Prop :=
  D.negativeLogPotential = -Real.log D.supervolume ∧
  calibratedStationary P ∧
  quaternion_field_residual nabla e_inv m Q gamma_action = 0

/-- Expand the packet into the exact finite scalar equalities and residual it asserts. -/
theorem quaternionCalibratedStationary_iff
    (D : NarainSupervolumeBridgeData n)
    (P : CalibrationVariationData) :
    quaternionCalibratedStationary nabla e_inv m gamma_action Q D P ↔
      (D.negativeLogPotential = -Real.log D.supervolume) ∧
      ((P.dMassieu - P.dKL - P.lambdaInc * P.dIncidenceFriction -
          P.lambdaFree * P.dFreeEnergy = 0) ∧
        (P.einsteinTensor =
          (8 * Real.pi * P.newtonG) * effectiveStressReadout P) ∧
        (P.boundaryEntropy = P.boundaryArea / (4 * P.boundaryNewtonG))) ∧
      (quaternion_field_residual nabla e_inv m Q gamma_action = 0) := by
  unfold quaternionCalibratedStationary
  rw [calibratedStationary_iff]

end

end InfoGeometry.Canonical.QuaternionCalibratedStationaryBridge
