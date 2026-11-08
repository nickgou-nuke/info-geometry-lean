/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.GenericMetriplecticFlow

namespace InfoGeometry.Thermo.GenericMetriplecticFlow.System

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A linear change of state coordinates preserves the energy rate as a scalar readout. -/
theorem transport_energy_rate_readback
    (S : System V) (e : V ≃ₗ[ℝ] W) :
    (S.transport e).dH ((S.transport e).flow) = S.dH S.flow := by
  rw [transport_flow]
  change (S.dH.comp e.symm.toLinearMap) (e S.flow) = S.dH S.flow
  simp

/-- A linear change of state coordinates preserves the entropy rate as a scalar readout. -/
theorem transport_entropy_rate_readback
    (S : System V) (e : V ≃ₗ[ℝ] W) :
    (S.transport e).dS ((S.transport e).flow) = S.dS S.flow := by
  rw [transport_flow]
  change (S.dS.comp e.symm.toLinearMap) (e S.flow) = S.dS S.flow
  simp

end InfoGeometry.Thermo.GenericMetriplecticFlow.System
