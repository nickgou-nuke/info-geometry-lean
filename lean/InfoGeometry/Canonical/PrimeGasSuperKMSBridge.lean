import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeGasSuperKMSBridge

Witness-gated bridge between a prime-gas max-entropy packet and a super-KMS
temperature packet.

This file deliberately does not import open-problem theorem packets. It stores
the necessary compatibility data explicitly and proves only consequences of the
stored fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeGasSuperKMSBridge

/-- Minimal owner-level prime-gas max-entropy packet. -/
@[rep_depth operator]
structure PrimeGasMaxEntPacket where
  partitionFunction : ℝ
  entropyReadout : ℝ
  freeEnergyReadout : ℝ

/-- Witness-gated Jaynes/Riemannian readout bridge. -/
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

namespace PrimeGasSuperKMSBridge

variable (B : PrimeGasSuperKMSBridge)

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

end InfoGeometry.Canonical.PrimeGasSuperKMSBridge
