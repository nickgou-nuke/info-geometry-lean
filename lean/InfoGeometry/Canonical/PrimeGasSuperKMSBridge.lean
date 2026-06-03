import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeGasSuperKMS

Witness-gated bridge between a prime-gas max-entropy packet and a super-KMS
temperature packet.

This file deliberately does not import open-problem theorem packets. It stores
the necessary compatibility data explicitly and proves only consequences of the
stored fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeGasSuperKMS

/-- Minimal owner-level prime-gas max-entropy packet. -/
@[rep_depth operator]
structure PrimeGasMaxEntPacket where
  partitionFunction : ℝ
  entropyReadout : ℝ
  freeEnergyReadout : ℝ

/-- witness-gated (Native Closure Mandated: Closure Debt) Jaynes/Riemannian readout bridge. -/
@[rep_depth operator]
structure PrimeGasJaynesRNBridge where
  jaynesEntropy : ℝ
  rnEntropy : ℝ
  jaynes_eq_rn :
    jaynesEntropy = rnEntropy

/-- Super-geometric temperature split into even and odd readouts. -/
@[rep_depth operator]
structure SuperGeometricTemperature where
  evenTemperature : ℝ
  oddTemperature : ℝ

/-- KMS target packet for the prime-gas bridge. -/
@[rep_depth operator]
structure PrimeGasKMSTargetBridge where
  superTemperature : SuperGeometricTemperature
  zero_odd :
    superTemperature.oddTemperature = 0
  absorption : ℝ
  spontaneousEmission : ℝ
  stimulatedEmission : ℝ
  detailedBalance :
    absorption = spontaneousEmission + stimulatedEmission

/-- Extract the super-geometric temperature from a KMS target packet. -/
def toSuperGeometricTemperature
    (K : PrimeGasKMSTargetBridge) : SuperGeometricTemperature :=
  K.superTemperature

@[simp]
theorem toSuperGeometricTemperature_eq
    (K : PrimeGasKMSTargetBridge) :
    toSuperGeometricTemperature K = K.superTemperature :=
  rfl

@[simp]
theorem toSuperGeometricTemperature_zero_odd
    (K : PrimeGasKMSTargetBridge) :
    (toSuperGeometricTemperature K).oddTemperature = 0 :=
  K.zero_odd

/--
Prime-gas/super-KMS bridge.

All cross-surface identifications are stored explicitly as witness fields.
-/
@[rep_depth operator]
structure PrimeGasSuperKMSBridge where
  primeGas : PrimeGasMaxEntPacket
  jaynesRN : PrimeGasJaynesRNBridge
  kmsTarget : PrimeGasKMSTargetBridge
  superTemperature : SuperGeometricTemperature
  superTemperature_eq :
    superTemperature = toSuperGeometricTemperature kmsTarget

/-- Witness-form compatibility surface for the super-temperature/KMS target match. -/
@[rep_depth operator]
structure SuperTemperatureCompatibilityWitness where
  kmsTarget : PrimeGasKMSTargetBridge
  superTemperature : SuperGeometricTemperature
  superTemperature_eq :
    superTemperature = toSuperGeometricTemperature kmsTarget

/-- Recover the compatibility equality from an explicit witness packet. -/
theorem superTemperature_eq_toSuperGeometricTemperature_of_witness
    (W : SuperTemperatureCompatibilityWitness) :
    W.superTemperature = toSuperGeometricTemperature W.kmsTarget :=
  W.superTemperature_eq

/-- Construct the witness-form compatibility packet from a bridge. -/
def PrimeGasSuperKMSBridge.toSuperTemperatureCompatibilityWitness
    (B : PrimeGasSuperKMSBridge) : SuperTemperatureCompatibilityWitness where
  kmsTarget := B.kmsTarget
  superTemperature := B.superTemperature
  superTemperature_eq := B.superTemperature_eq

/-- Witness-routed readback of the bridge temperature/KMS compatibility. -/
theorem PrimeGasSuperKMSBridge.superTemperature_eq_toSuperGeometricTemperature_viaWitness
    (B : PrimeGasSuperKMSBridge) :
    B.superTemperature = toSuperGeometricTemperature B.kmsTarget := by
  exact superTemperature_eq_toSuperGeometricTemperature_of_witness
    (B.toSuperTemperatureCompatibilityWitness)

namespace PrimeGasSuperKMSBridge

variable (B : PrimeGasSuperKMSBridge)

/-- The bridge's stored super-temperature is exactly the KMS target temperature. -/
@[simp]
theorem superTemperature_eq_kmsTargetTemperature :
    B.superTemperature = B.kmsTarget.superTemperature := by
  rw [B.superTemperature_eq, toSuperGeometricTemperature_eq]

/-- The bridge's super-temperature is the same as the extracted KMS temperature. -/
@[simp]
theorem superTemperature_eq_toSuperGeometricTemperature :
    B.superTemperature = toSuperGeometricTemperature B.kmsTarget := by
  rw [B.superTemperature_eq]

/-- The odd super-temperature vanishes by the stored KMS witness. -/
@[simp]
theorem superTemperature_odd_eq_zero :
    B.superTemperature.oddTemperature = 0 := by
  rw [B.superTemperature_eq]
  exact toSuperGeometricTemperature_zero_odd B.kmsTarget

/-- Detailed balance is exposed directly from the KMS target packet. -/
theorem detailedBalance :
    B.kmsTarget.absorption =
      B.kmsTarget.spontaneousEmission + B.kmsTarget.stimulatedEmission :=
  B.kmsTarget.detailedBalance

/-- The Jaynes and RN entropy readouts agree by the stored witness. -/
theorem jaynesEntropy_eq_rnEntropy :
    B.jaynesRN.jaynesEntropy = B.jaynesRN.rnEntropy :=
  B.jaynesRN.jaynes_eq_rn

end PrimeGasSuperKMSBridge

end InfoGeometry.Canonical.PrimeGasSuperKMS
