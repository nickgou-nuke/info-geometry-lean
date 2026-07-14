import InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace ModularHamiltonianSurrogateCalibration

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge

section Calibration

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
Witness-gated calibration of a state-space modular flow by the bounded
supercharge modular-Hamiltonian surrogate `K_sur`.

This structure does not construct the Tomita modular operator `Δ`, does not
assert `Q² = Δ`, and does not identify `K_sur` with `-log Δ`.  It records only
that a supplied modular-flow action is calibrated to a supplied `K_sur` action
on the chosen state carrier.
-/
@[rep_depth operator]
structure Calibration where
  /-- Bounded Drazin/MP supercharge modular-Hamiltonian surrogate. -/
  bridge : SuperchargeModularHamiltonianBridge.Bridge (E := E)

  /-- Supplied modular-flow action on the chosen state carrier. -/
  modularFlow : ℝ → State → State

  /-- Supplied `K_sur`-generated action on the same state carrier. -/
  KsurFlow : ℝ → State → State

  /-- Zero-time identity law for the supplied modular flow. -/
  modularFlow_zero : ∀ s : State, modularFlow 0 s = s

  /-- Additive one-parameter law for the supplied modular flow. -/
  modularFlow_add :
    ∀ (t u : ℝ) (s : State),
      modularFlow (t + u) s = modularFlow t (modularFlow u s)

  /-- Calibration witness: the modular flow is the `K_sur` action. -/
  Ksur_calibrates_modularFlow :
    ∀ (t : ℝ) (s : State), modularFlow t s = KsurFlow t s

namespace Calibration

variable (C : Calibration (E := E) (State := State))

/-- The calibrated bounded generator is exactly the bridge's `K_sur`. -/
@[rep_depth operator]
def calibratedGenerator : EndH :=
  C.bridge.Ksur

/-- Readback: `K_sur` is the calibrated regular-restricted super-Hamiltonian. -/
@[rep_depth operator]
theorem calibratedGenerator_eq_calibrated_regularRestrictedSuperHamiltonian :
    calibratedGenerator C =
      C.bridge.modularEnergyUnit •
        DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian
          C.bridge.CIK := by
  unfold calibratedGenerator
  exact C.bridge.Ksur_eq_calibrated_regularRestrictedSuperHamiltonian

/-- Zero-time modular flow readback. -/
@[rep_depth operator]
theorem modularFlow_zero_apply (s : State) :
    C.modularFlow 0 s = s :=
  C.modularFlow_zero s

/-- Additive time-composition readback. -/
@[rep_depth operator]
theorem modularFlow_add_apply (t u : ℝ) (s : State) :
    C.modularFlow (t + u) s = C.modularFlow t (C.modularFlow u s) :=
  C.modularFlow_add t u s

/-- Calibration readback: the supplied modular flow is the supplied `K_sur` flow. -/
@[rep_depth operator]
theorem modularFlow_eq_KsurFlow (t : ℝ) (s : State) :
    C.modularFlow t s = C.KsurFlow t s :=
  C.Ksur_calibrates_modularFlow t s

/-- The calibrated generator is supported on the Drazin regular projector on the left. -/
@[rep_depth operator]
theorem spectralProjector_mul_calibratedGenerator :
    C.bridge.CIK.spectralProjector * calibratedGenerator C =
      calibratedGenerator C := by
  unfold calibratedGenerator
  exact C.bridge.spectralProjector_mul_Ksur

/-- The calibrated generator is supported on the Drazin regular projector on the right. -/
@[rep_depth operator]
theorem calibratedGenerator_mul_spectralProjector :
    calibratedGenerator C * C.bridge.CIK.spectralProjector =
      calibratedGenerator C := by
  unfold calibratedGenerator
  exact C.bridge.Ksur_mul_spectralProjector

/-- The calibrated generator is left-annihilated by the Drazin defect projector. -/
@[rep_depth operator]
theorem spectralComplementaryProjector_mul_calibratedGenerator_eq_zero :
    C.bridge.CIK.spectralComplementaryProjector * calibratedGenerator C = 0 := by
  unfold calibratedGenerator
  exact C.bridge.spectralComplementaryProjector_mul_Ksur_eq_zero

/-- The calibrated generator is right-annihilated by the Drazin defect projector. -/
@[rep_depth operator]
theorem calibratedGenerator_mul_spectralComplementaryProjector_eq_zero :
    calibratedGenerator C * C.bridge.CIK.spectralComplementaryProjector = 0 := by
  unfold calibratedGenerator
  exact C.bridge.Ksur_mul_spectralComplementaryProjector_eq_zero

/-- The calibrated generator commutes with the spectral grading. -/
@[rep_depth operator]
theorem calibratedGenerator_commutes_GammaS :
    calibratedGenerator C * C.bridge.CIK.GammaS =
      C.bridge.CIK.GammaS * calibratedGenerator C := by
  unfold calibratedGenerator
  exact C.bridge.Ksur_commutes_GammaS

/-- The calibrated generator is spectrally compact/even. -/
@[rep_depth operator]
theorem calibratedGenerator_isSpectralCompact :
    let T := C.bridge.CIK.toInformationCartanTriple
    T.IsSpectralCompact (calibratedGenerator C) := by
  unfold calibratedGenerator
  exact C.bridge.Ksur_isSpectralCompact

/--
Package theorem: `K_sur` is bounded by construction, regular-supported,
defect-annihilating, and in the even/spectrally compact lane.
-/
@[rep_depth operator]
theorem Ksur_regular_support_even_package :
    (C.bridge.CIK.spectralProjector * calibratedGenerator C =
        calibratedGenerator C)
      ∧ (calibratedGenerator C * C.bridge.CIK.spectralProjector =
          calibratedGenerator C)
      ∧ (C.bridge.CIK.spectralComplementaryProjector *
          calibratedGenerator C = 0)
      ∧ (calibratedGenerator C *
          C.bridge.CIK.spectralComplementaryProjector = 0)
      ∧ (let T := C.bridge.CIK.toInformationCartanTriple;
          T.IsSpectralCompact (calibratedGenerator C)) := by
  exact ⟨spectralProjector_mul_calibratedGenerator C,
    calibratedGenerator_mul_spectralProjector C,
    spectralComplementaryProjector_mul_calibratedGenerator_eq_zero C,
    calibratedGenerator_mul_spectralComplementaryProjector_eq_zero C,
    calibratedGenerator_isSpectralCompact C⟩

end Calibration

end Calibration

end ModularHamiltonianSurrogateCalibration

end
