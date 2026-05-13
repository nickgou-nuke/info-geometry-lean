import InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.BoundedModularFlowCalibration

open InfoGeometry.Canonical

variable {E State : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Witness-gated calibration of an external bounded modular flow against the
Drazin/MP supercharge Hamiltonian surrogate.

This is deliberately not a construction of Tomita--Takesaki modular flow.  It
only records that a separately supplied flow agrees with a separately supplied
action of the bounded surrogate `Ksur`.
-/
@[rep_depth krein]
structure BoundedModularFlowCalibration where
  bridge : SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge (E := E)

  /-- External bounded flow to be calibrated. -/
  flow : ℝ → State → State

  /-- Action generated/read by the bounded surrogate `Ksur`. -/
  KsurAction : ℝ → State → State

  /-- The supplied flow agrees with the supplied bounded-surrogate action. -/
  flow_eq_KsurAction : ∀ t s, flow t s = KsurAction t s

namespace BoundedModularFlowCalibration

variable (C : BoundedModularFlowCalibration (E := E) (State := State))

/-- The calibrated generator is the bounded supercharge modular-Hamiltonian surrogate. -/
@[rep_depth krein]
def calibratedGenerator : EndH :=
  C.bridge.Ksur

/-- Generator readback: `K_cal = μ_Q • P_D Q² P_D`. -/
@[rep_depth krein]
theorem calibratedGenerator_eq_calibrated_regularRestrictedSuperHamiltonian :
    calibratedGenerator C =
      C.bridge.modularEnergyUnit •
        DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian C.bridge.CIK := by
  unfold calibratedGenerator
  exact
    SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge.Ksur_eq_calibrated_regularRestrictedSuperHamiltonian
      C.bridge

/-- Calibrated flow readback. -/
@[rep_depth krein]
theorem flow_eq_action (t : ℝ) (s : State) :
    C.flow t s = C.KsurAction t s :=
  C.flow_eq_KsurAction t s

/-- The calibrated generator is left-supported on the Drazin regular projector. -/
@[rep_depth krein]
theorem spectralProjector_mul_calibratedGenerator :
    C.bridge.CIK.spectralProjector * calibratedGenerator C = calibratedGenerator C := by
  unfold calibratedGenerator
  exact
    SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge.spectralProjector_mul_Ksur
      C.bridge

/-- The calibrated generator is right-supported on the Drazin regular projector. -/
@[rep_depth krein]
theorem calibratedGenerator_mul_spectralProjector :
    calibratedGenerator C * C.bridge.CIK.spectralProjector = calibratedGenerator C := by
  unfold calibratedGenerator
  exact
    SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge.Ksur_mul_spectralProjector
      C.bridge

/-- The calibrated generator is annihilated by the defect projector on the left. -/
@[rep_depth krein]
theorem spectralComplementaryProjector_mul_calibratedGenerator_eq_zero :
    C.bridge.CIK.spectralComplementaryProjector * calibratedGenerator C = 0 := by
  unfold calibratedGenerator
  exact
    SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge.spectralComplementaryProjector_mul_Ksur_eq_zero
      C.bridge

/-- The calibrated generator is annihilated by the defect projector on the right. -/
@[rep_depth krein]
theorem calibratedGenerator_mul_spectralComplementaryProjector_eq_zero :
    calibratedGenerator C * C.bridge.CIK.spectralComplementaryProjector = 0 := by
  unfold calibratedGenerator
  exact
    SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge.Ksur_mul_spectralComplementaryProjector_eq_zero
      C.bridge

/-- The calibrated generator remains in the even/spectrally compact lane. -/
@[rep_depth krein]
theorem calibratedGenerator_isSpectralCompact :
    let T := C.bridge.CIK.toInformationCartanTriple
    T.IsSpectralCompact (calibratedGenerator C) := by
  unfold calibratedGenerator
  exact
    SuperchargeModularHamiltonianBridge.SuperchargeModularHamiltonianBridge.Ksur_isSpectralCompact
      C.bridge

end BoundedModularFlowCalibration

end InfoGeometry.Canonical.BoundedModularFlowCalibration
