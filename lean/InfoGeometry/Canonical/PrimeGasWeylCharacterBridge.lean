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
abbrev PrimeGasWeylData := ℝ × (ℝ × (ℝ × ℝ))

namespace PrimeGasWeylData

abbrev beta (P : PrimeGasWeylData) : ℝ := P.1

abbrev partitionFunction (P : PrimeGasWeylData) : ℝ := P.2.1

abbrev entropyReadout (P : PrimeGasWeylData) : ℝ := P.2.2.1

abbrev characterReadout (P : PrimeGasWeylData) : ℝ := P.2.2.2

end PrimeGasWeylData

/-- Minimal Souriau thermodynamic readout packet. -/
@[rep_depth operator]
abbrev SouriauThermodynamicPacket := ℝ × ℝ

namespace SouriauThermodynamicPacket

abbrev beta (P : SouriauThermodynamicPacket) : ℝ := P.1

abbrev entropyReadout (P : SouriauThermodynamicPacket) : ℝ := P.2

end SouriauThermodynamicPacket

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

namespace PrimeGasWeylCharacterBridge

variable (B : PrimeGasWeylCharacterBridge)

/-- Weyl-character readout supplied by the prime-gas owner. -/
abbrev weylCharacter (B : PrimeGasWeylCharacterBridge) : ℝ :=
  B.primeGas.characterReadout

@[simp] theorem weylCharacter_eq (B : PrimeGasWeylCharacterBridge) :
    B.weylCharacter = B.primeGas.characterReadout :=
  rfl

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

/-- Canonical theorem-backed constructor from prime-gas data. -/
def ofPrimeGas (P : PrimeGasWeylData) : PrimeGasWeylCharacterBridge where
  primeGas := P
  souriau := ⟨P.beta, P.entropyReadout⟩
  beta_eq := rfl
  entropy_eq := rfl

@[simp]
theorem ofPrimeGas_beta (P : PrimeGasWeylData) :
    (ofPrimeGas P).souriau.beta = P.beta := rfl

@[simp]
theorem ofPrimeGas_entropy (P : PrimeGasWeylData) :
    (ofPrimeGas P).souriau.entropyReadout = P.entropyReadout := rfl

@[simp]
theorem ofPrimeGas_weylCharacter (P : PrimeGasWeylData) :
    (ofPrimeGas P).weylCharacter = P.characterReadout := rfl

end PrimeGasWeylCharacterBridge

end InfoGeometry.Canonical.PrimeGasWeylCharacter
