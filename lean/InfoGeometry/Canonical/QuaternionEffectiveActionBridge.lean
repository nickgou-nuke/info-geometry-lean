import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebraic.NarainSupervolumeBridgeData
import InfoGeometry.Canonical.QuaternionGeometry
import InfoGeometry.Physics.FreeEntropyCalibrationVariationPacket

/-!
# InfoGeometry.Canonical.QuaternionEffectiveActionBridge

This is a theorem-safe finite bridge between three already-owned surfaces:

* `NarainSupervolumeBridgeData`: effective action as a negative logarithm of a
  positive readout;
* `FreeEntropyCalibrationVariationPacket`: explicit stationarity residual;
* `QuaternionGeometry`: quaternion field-equation residual equivalence.

It does not derive a path integral, Hessian one-loop determinant, RG beta
functions, non-perturbative flow equation, or black-hole evaporation law.
-/

noncomputable section

open InfoGeometry.Physics.FreeEntropyCalibrationVariationPacket

namespace InfoGeometry.Canonical.QuaternionEffectiveActionBridge

open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Canonical.QuaternionGeometry

/-- Re-export the negative-log effective-action law from the Narain/supervolume owner. -/
theorem effectiveAction_eq_negativeLogReadout
    {n : ℕ} (D : NarainSupervolumeBridgeData n) :
    D.negativeLogPotential = -Real.log D.supervolume := by
  exact D.effectiveAction_eq_negLog

section QuaternionStationary

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

/-- Honest finite conjunction for the quaternion effective/stationary bridge. -/
def quantumStationaryBridge
    (D : NarainSupervolumeBridgeData n)
    (P : CalibrationVariationPacket) : Prop :=
  D.negativeLogPotential = -Real.log D.supervolume ∧
  S_freeFirstVariation P = 0 ∧
  quaternion_field_residual nabla e_inv m Q gamma_action = 0

/-- Expands the finite bridge into the explicit scalar equalities it asserts. -/
theorem quantumStationaryBridge_iff
    (D : NarainSupervolumeBridgeData n)
    (P : CalibrationVariationPacket) :
    quantumStationaryBridge nabla e_inv m gamma_action Q D P ↔
      (D.negativeLogPotential = -Real.log D.supervolume) ∧
      (P.dMassieu - P.dKL - P.lambdaInc * P.dIncidenceFriction -
          P.lambdaFree * P.dFreeEnergy = 0) ∧
      (quaternion_field_residual nabla e_inv m Q gamma_action = 0) := by
  unfold quantumStationaryBridge
  rw [S_free_stationary_iff]

end QuaternionStationary

end InfoGeometry.Canonical.QuaternionEffectiveActionBridge
