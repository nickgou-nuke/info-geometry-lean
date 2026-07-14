import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Krein.Thermal
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge

Downstream KMS compatibility bridge for spectroscopic readout surfaces.

This file is a translator/coherence lane. It does **not** introduce a new KMS
owner. The owner remains `InfoGeometry.Dynamics.UnruhKMS`:

- `modularHamiltonian := boostGenerator`
- `unruhFlow θ := cosh θ · Id + sinh θ · modularHamiltonian`

The bridge only packages state-functionals that are compatible with that owned
modular-flow lane.
-/

namespace SpectroscopicGaugeKMSBridge

open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Compatibility predicate: a state-functional is KMS-like for the owned
Unruh modular Hamiltonian lane.
-/
@[rep_depth transport]
noncomputable def satisfiesOwnedUnruhKMS
    (ω : EndH →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  satisfies_kms_like
    (E := E)
    (InfoGeometry.Dynamics.modularHamiltonian (E := E))
    ω β

/--
Spectroscopic KMS-compatibility package.

This is downstream compatibility data, not a new thermodynamic owner.
-/
@[rep_depth transport]
structure SpectroscopicKMSCompatible where
  state : EndH →L[ℝ] ℝ
  inverseTemperature : ℝ
  compatible_with_owned_unruh_flow :
    satisfiesOwnedUnruhKMS (E := E) state inverseTemperature

/-- Expanded compatibility identity at the declared inverse temperature. -/
@[rep_depth transport]
theorem SpectroscopicKMSCompatible.kms_identity
    (kms : SpectroscopicKMSCompatible (E := E))
    (A B : EndH) :
    kms.state
      (A * modular_shift
        (E := E)
        (InfoGeometry.Dynamics.modularHamiltonian (E := E))
        kms.inverseTemperature B)
      =
    kms.state (B * A) := by
  let _ : CompleteSpace E := inferInstance
  exact kms.compatible_with_owned_unruh_flow A B

/-- Re-export of the owner modular-flow law for bridge users. -/
@[rep_depth transport]
theorem owned_unruhFlow_expansion (θ : ℝ) :
    InfoGeometry.Dynamics.unruhFlow (E := E) θ =
      (Real.cosh θ) • ContinuousLinearMap.id ℝ H₂
        + (Real.sinh θ) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  exact InfoGeometry.Dynamics.unruhFlow_is_modular_flow (E := E) θ

end Core

end SpectroscopicGaugeKMSBridge
