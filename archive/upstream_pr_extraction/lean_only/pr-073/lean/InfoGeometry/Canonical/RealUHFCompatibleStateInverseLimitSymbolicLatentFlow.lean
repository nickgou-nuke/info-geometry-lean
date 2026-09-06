import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological
import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
import InfoGeometry.Topology.SymbolicLatentModularFlow

/-!
# Symbolic-latent flow adapter for compatible state/readout families

The compatible-family carrier already has a continuous scalar pullback action.
This owner exposes that action through the generic symbolic-latent flow API.
It remains purely topological: no state positivity, KMS condition, C*-completion,
or completed inverse-limit algebra is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow

open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Topology

noncomputable def scalarDilationCompatibleReadoutFamilyFlow :
    SymbolicLatentModularFlow CompatibleContinuousReadoutFamily where
  act := fun t ρ => scalarDilationTopCatAction t ρ
  continuous_act := by
    simpa [scalarDilationTopCatAction_apply] using
      continuous_scalarDilation_pullback
  zero_apply := by
    intro ρ
    have h := scalarDilationTopCatAction_zero
    exact congrArg (fun f => f ρ) h
  add_apply := by
    intro s t ρ
    have h := scalarDilation_pullback_add_action t s ρ
    simpa [add_comm] using h

@[simp] theorem scalarDilationCompatibleReadoutFamilyFlow_apply
    (t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    scalarDilationCompatibleReadoutFamilyFlow.act t ρ =
      scalarDilationTopCatAction t ρ := rfl

theorem scalarDilationCompatibleReadoutFamilyFlow_orbit_mem
    (ρ : CompatibleContinuousReadoutFamily) :
    ρ ∈ scalarDilationCompatibleReadoutFamilyFlow.orbit ρ :=
  scalarDilationCompatibleReadoutFamilyFlow.orbit_mem ρ

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow

end
