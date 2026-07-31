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

/-- Prime-gas/super-KMS bridge using the KMS target as temperature owner. -/
@[rep_depth operator]
structure PrimeGasSuperKMSBridge where
  primeGas : PrimeGasMaxEntPacket
  jaynesRN : PrimeGasJaynesRNBridge
  kmsTarget : PrimeGasKMSTargetBridge

/-- The bridge temperature is canonically the temperature owned by its KMS target. -/
def PrimeGasSuperKMSBridge.superTemperature
    (B : PrimeGasSuperKMSBridge) : SuperGeometricTemperature :=
  B.kmsTarget.superTemperature

namespace PrimeGasSuperKMSBridge

variable (B : PrimeGasSuperKMSBridge)

/-- The odd super-temperature vanishes by the stored KMS witness. -/
@[simp]
theorem superTemperature_odd_eq_zero :
    B.superTemperature.oddTemperature = 0 :=
  B.kmsTarget.zero_odd

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
