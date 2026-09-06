import InfoGeometry.Canonical.ModularSuperchargeClosure
import InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.StateIndexedModularSeedBridge

State-indexed GA-native modular-seed bridge on the doubled real carrier.

This file is a translator/coherence surface:
- it derives a state-indexed seed presentation from the owned KMS lane,
- it does not replace canonical owners,
- and it proves equality to `canonicalModularSeed` under an explicit bounded
  compatibility property.
-/

namespace InfoGeometry.Canonical.StateIndexedModularSeedBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ModularSuperchargeClosure
open InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
State-indexed input packet:
- a property inverse-kernel lane property,
- and a KMS-compatible state-functional packet on the owned Unruh lane.
-/
@[rep_depth transport]
structure StateIndexedSeedDatum where
  CIK : CertifiedInverseKernel H₂
  kms : SpectroscopicKMSCompatible (E := E)

/--
State-indexed boost generator on the owned KMS lane.

The inverse-temperature is kept explicit as a scalar readout of the
state-functional packet.
-/
@[rep_depth transport]
noncomputable def stateIndexedBoostGenerator
    (D : StateIndexedSeedDatum (E := E)) : EndH :=
  (D.kms.inverseTemperature * (2 * Real.pi)) • InfoGeometry.Dynamics.modularHamiltonian (E := E)

/--
State-indexed bivector seed surface in GA-native language:
`δ_state := -(H_state ∘ (J∘ε))`.
-/
@[rep_depth transport]
noncomputable def stateIndexedBivectorSeed
    (D : StateIndexedSeedDatum (E := E)) : EndH :=
  -((stateIndexedBoostGenerator (E := E) D).comp (InfoGeometry.Krein.clockAxis (E := E)))

/--
Transport-generator recovery on the state-indexed seed surface:
`modularTransportGenerator(δ_state) = H_state`.
-/
@[rep_depth transport]
theorem modularTransportGenerator_stateIndexedBivectorSeed
    (D : StateIndexedSeedDatum (E := E)) :
    modularTransportGenerator (E := E) (stateIndexedBivectorSeed (E := E) D)
      =
    stateIndexedBoostGenerator (E := E) D := by
  set H : EndH := stateIndexedBoostGenerator (E := E) D
  set K : EndH := InfoGeometry.Krein.clockAxis (E := E)
  have hK2 : K.comp K = -(ContinuousLinearMap.id ℝ H₂) := by
    subst K
    exact InfoGeometry.Krein.clockAxis_sq (E := E)
  calc
    modularTransportGenerator (E := E) (stateIndexedBivectorSeed (E := E) D)
        = (-(H.comp K)).comp K := by
            simp [stateIndexedBivectorSeed, modularTransportGenerator, H, K]
    _ = -((H.comp K).comp K) := by simp
    _ = -(H.comp (K.comp K)) := by simp [ContinuousLinearMap.comp_assoc]
    _ = -(H.comp (-(ContinuousLinearMap.id ℝ H₂))) := by rw [hK2]
    _ = -(-(H.comp (ContinuousLinearMap.id ℝ H₂))) := by simp
    _ = H := by simp

/-- On bounded witnesses, the state-indexed boost generator is exactly `H_D`. -/
@[rep_depth transport]
theorem stateIndexedBoostGenerator_eq_superHamiltonian_of_boundedWitness
    (datum : StateIndexedSeedDatum (E := E))
    (hInverseTemperature_one : datum.kms.inverseTemperature = 1)
    (hTwoPi_calibration :
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK datum.CIK =
        (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) :
    stateIndexedBoostGenerator (E := E) datum
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK datum.CIK := by
  calc
    stateIndexedBoostGenerator (E := E) datum
        =
      (datum.kms.inverseTemperature * (2 * Real.pi))
        • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
          rfl
    _ = (1 * (2 * Real.pi)) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
          simp [hInverseTemperature_one]
    _ = (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
          simp
    _ = DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK datum.CIK := by
          simpa using hTwoPi_calibration.symm

/--
Capstone translator theorem:
on bounded witnesses, the state-indexed GA seed equals the canonical
projected-even modular seed.
-/
@[rep_depth transport]
theorem stateIndexedBivectorSeed_eq_canonicalModularSeed_of_boundedWitness
    (datum : StateIndexedSeedDatum (E := E))
    (hInverseTemperature_one : datum.kms.inverseTemperature = 1)
    (hTwoPi_calibration :
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK datum.CIK =
        (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) :
    stateIndexedBivectorSeed (E := E) datum
      =
    canonicalBivectorSeed (E := E) datum.CIK := by
  have hGen :
      stateIndexedBoostGenerator (E := E) datum
        =
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK datum.CIK :=
    stateIndexedBoostGenerator_eq_superHamiltonian_of_boundedWitness (E := E) datum
      hInverseTemperature_one hTwoPi_calibration
  unfold stateIndexedBivectorSeed canonicalBivectorSeed
  simp [hGen]

/--
Transport-generator equivalence on bounded witnesses:
state-indexed seed and canonical seed induce the same modular generator.
-/
@[rep_depth transport]
theorem stateIndexed_transportGenerator_eq_canonical_of_boundedWitness
    (datum : StateIndexedSeedDatum (E := E))
    (hInverseTemperature_one : datum.kms.inverseTemperature = 1)
    (hTwoPi_calibration :
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK datum.CIK =
        (2 * Real.pi) • InfoGeometry.Dynamics.modularHamiltonian (E := E)) :
    modularTransportGenerator (E := E) (stateIndexedBivectorSeed (E := E) datum)
      =
    modularTransportGenerator (E := E) (canonicalBivectorSeed (E := E) datum.CIK) := by
  rw [stateIndexedBivectorSeed_eq_canonicalModularSeed_of_boundedWitness (E := E) datum
    hInverseTemperature_one hTwoPi_calibration]

end Core

end InfoGeometry.Canonical.StateIndexedModularSeedBridge
