import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeGasWeylCharacter

Witness-gated prime-gas/Weyl-character bridge.

This file does not depend on open-problem namespaces or external Souriau
theorem packets. It stores the Weyl-character and thermodynamic comparison
data explicitly.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeGasWeylCharacter

/-- Raw prime-gas data used by the Weyl-character bridge. -/
@[rep_depth operator]
structure PrimeGasWeylData where
  beta : ℝ
  partitionFunction : ℝ
  entropyReadout : ℝ
  characterReadout : ℝ

/-- Minimal Souriau thermodynamic readout packet. -/
@[rep_depth operator]
structure SouriauThermodynamicPacket where
  beta : ℝ
  entropyReadout : ℝ

/--
Witness-gated Weyl-character bridge.

The bridge stores the comparison between the prime-gas data and the Souriau
thermodynamic readout explicitly.
-/
@[rep_depth operator]
structure PrimeGasWeylCharacterBridge where
  primeGas : PrimeGasWeylData
  souriau : SouriauThermodynamicPacket
  beta_eq :
    souriau.beta = primeGas.beta
  entropy_eq :
    souriau.entropyReadout = primeGas.entropyReadout
  weylCharacter : ℝ
  weylCharacter_eq :
    weylCharacter = primeGas.characterReadout

namespace PrimeGasWeylCharacterBridge

variable (B : PrimeGasWeylCharacterBridge)

/-- The Souriau inverse-temperature readout matches the prime-gas beta. -/
@[simp]
theorem souriau_beta_eq_primeGas_beta :
    B.souriau.beta = B.primeGas.beta :=
  B.beta_eq

/-- The Souriau entropy readout matches the prime-gas entropy readout. -/
@[simp]
theorem souriau_entropy_eq_primeGas_entropy :
    B.souriau.entropyReadout = B.primeGas.entropyReadout :=
  B.entropy_eq

/-- The Weyl-character readout is the stored prime-gas character readout. -/
@[simp]
theorem weylCharacter_eq_primeGas_character :
    B.weylCharacter = B.primeGas.characterReadout :=
  B.weylCharacter_eq

end PrimeGasWeylCharacterBridge

end InfoGeometry.Canonical.PrimeGasWeylCharacter
