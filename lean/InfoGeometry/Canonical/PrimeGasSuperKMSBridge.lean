import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeGasSuperKMS

Bridge between a prime-gas max-entropy packet and a super-KMS temperature
packet.

The super-temperature is owned by the KMS target.  It is not duplicated in the
bridge and no separate compatibility witness is required.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeGasSuperKMS

/-- Minimal owner-level prime-gas max-entropy packet. -/
@[rep_depth operator]
structure PrimeGasMaxEntPacket where
  partitionFunction : ℝ
  entropyReadout : ℝ
  freeEnergyReadout : ℝ

/-- Native equality relation between the Jaynes and RN entropy readouts. -/
@[rep_depth operator]
abbrev PrimeGasJaynesRNBridge :=
  {readouts : ℝ × ℝ // readouts.1 = readouts.2}

namespace PrimeGasJaynesRNBridge

abbrev jaynesEntropy (B : PrimeGasJaynesRNBridge) : ℝ :=
  B.1.1

abbrev rnEntropy (B : PrimeGasJaynesRNBridge) : ℝ :=
  B.1.2

theorem jaynes_eq_rn (B : PrimeGasJaynesRNBridge) :
    B.jaynesEntropy = B.rnEntropy :=
  B.2

end PrimeGasJaynesRNBridge

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

/-- Prime-gas/super-KMS bridge using the KMS target as temperature owner. -/
@[rep_depth operator]
structure PrimeGasSuperKMSBridge where
  primeGas : PrimeGasMaxEntPacket
  jaynesRN : PrimeGasJaynesRNBridge
  kmsTarget : PrimeGasKMSTargetBridge

/-- The bridge temperature is canonically the temperature owned by its KMS target. -/
def PrimeGasSuperKMSBridge.superTemperature
    (B : PrimeGasSuperKMSBridge) : SuperGeometricTemperature :=
  toSuperGeometricTemperature B.kmsTarget

/--
Compatibility is reflexivity for the canonical KMS-owned temperature.

The historical theorem name is retained for downstream compatibility; no
witness packet is involved.
-/
theorem superTemperature_eq_toSuperGeometricTemperature_of_witness
    (K : PrimeGasKMSTargetBridge) :
    toSuperGeometricTemperature K = K.superTemperature :=
  toSuperGeometricTemperature_eq K

/--
Historical compatibility name, now exposing the canonical equality directly
instead of constructing an evidence record.
-/
theorem PrimeGasSuperKMSBridge.toSuperTemperatureCompatibilityWitness
    (B : PrimeGasSuperKMSBridge) :
    B.superTemperature = toSuperGeometricTemperature B.kmsTarget :=
  rfl

/-- Direct readback of the bridge temperature/KMS compatibility. -/
theorem PrimeGasSuperKMSBridge.superTemperature_eq_toSuperGeometricTemperature_viaWitness
    (B : PrimeGasSuperKMSBridge) :
    B.superTemperature = toSuperGeometricTemperature B.kmsTarget :=
  B.toSuperTemperatureCompatibilityWitness

namespace PrimeGasSuperKMSBridge

variable (B : PrimeGasSuperKMSBridge)

/-- The bridge's stored super-temperature is exactly the KMS target temperature. -/
@[simp]
theorem superTemperature_eq_kmsTargetTemperature :
    B.superTemperature = B.kmsTarget.superTemperature :=
  rfl

/-- The bridge's super-temperature is the same as the extracted KMS temperature. -/
@[simp]
theorem superTemperature_eq_toSuperGeometricTemperature :
    B.superTemperature = toSuperGeometricTemperature B.kmsTarget :=
  rfl

/-- The odd super-temperature vanishes by the stored KMS witness. -/
@[simp]
theorem superTemperature_odd_eq_zero :
    B.superTemperature.oddTemperature = 0 :=
  toSuperGeometricTemperature_zero_odd B.kmsTarget

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
