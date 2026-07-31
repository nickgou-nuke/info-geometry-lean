import InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge
import InfoGeometry.Canonical.WeylCharacterEquivalence

/-!
# InfoGeometry.Canonical.BinaryCrystalHamiltonianFlow

Bridge packet for the binary crystal and the thermodynamic flow partition.

This file does not re-prove the Hamiltonian-flow layer already owned by
`InfoGeometry.Dynamics.HamiltonianFlowBridge`.  It packages the binary crystal
owner target together with the Souriau/Weyl packets and the thermodynamic
partition bridge so the dynamic corridor has a binary-crystal entry point.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryCrystalHamiltonianFlow

open InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge
open InfoGeometry.Canonical.WeylCharacterEquivalence

variable {𝔤 : Type*}

/--
Binary crystal / thermodynamic flow packet.

The symbolic side is the binary-crystal owner target plus the Souriau/Weyl
character packet.  The thermodynamic side is the positive-root partition bridge
used by the Hamiltonian-flow layer.
-/
@[rep_depth transport]
structure BinaryCrystalHamiltonianFlowBridge
    (𝔤 : Type*) where
  /-- Binary-crystal owner target. -/
  crystalOwner : BinaryCrystalWeylBlochOwnerTarget

  /-- Souriau/Weyl finite character packet. -/
  souriauPacket : SouriauWeylPartitionPacket 𝔤

namespace BinaryCrystalHamiltonianFlowBridge

variable (B : BinaryCrystalHamiltonianFlowBridge 𝔤)

/-- The binary crystal packet still supplies the binary-owner target. -/
@[rep_depth transport]
theorem crystal_ownerTarget :
    (∀ w : BinaryLattice,
      binaryUnitCell w =
        ({w} : Set BinaryLattice)
          ∪ binaryUnitCell (TypeIIIModularCantorSystem.BinaryWord.child w false)
          ∪ binaryUnitCell (TypeIIIModularCantorSystem.BinaryWord.child w true))
    ∧ (∀ w : BinaryLattice, ∀ b : Bool,
        wordParity (TypeIIIModularCantorSystem.BinaryWord.child w b) = not (wordParity w))
    ∧ (∀ {G : Type*} [Group G] [MulAction G BinaryLattice]
        (g : G) (f : BinaryCrystalObservable) (w : BinaryLattice),
        adjointAction (G := G) g f (g • w) = f w) :=
  binaryCrystalWeylBlochOwnerTarget

/-- The Souriau partition function is read as a Souriau character on the crystal side. -/
@[rep_depth transport]
theorem partitionFunction_is_souriau_character (B : BinaryCrystalHamiltonianFlowBridge
    𝔤) :
    B.souriauPacket.representation.partitionFunction B.souriauPacket.beta =
      B.souriauPacket.representation.character
        (B.souriauPacket.representation.thermalElement
          B.souriauPacket.beta) :=
  B.souriauPacket.representation.partitionFunction_eq_character B.souriauPacket.beta

/-- The Weyl denominator remains the prime Euler product on the crystal side. -/
@[rep_depth transport]
theorem denominator_is_prime_euler_product (B : BinaryCrystalHamiltonianFlowBridge
    𝔤) :
    B.souriauPacket.denominatorBridge.weylDenominator =
      B.souriauPacket.denominatorBridge.primeEulerProduct :=
  B.souriauPacket.denominatorBridge.weylDenominator_eq_primeEulerProduct

end BinaryCrystalHamiltonianFlowBridge

end InfoGeometry.Canonical.BinaryCrystalHamiltonianFlow
