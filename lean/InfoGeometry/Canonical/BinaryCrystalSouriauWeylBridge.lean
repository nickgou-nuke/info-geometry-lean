import InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge
import InfoGeometry.Canonical.WeylCharacterEquivalence

/-!
# InfoGeometry.Canonical.BinaryCrystalSouriauWeyl

Specialization bridge for the binary-fractal crystal and Souriau/Weyl
partition surface.

This file bundles the repo-owned binary crystal packet with the repo-owned
Souriau/Weyl partition packet.  It deliberately does not re-export the
Souriau/Weyl theorem fields through another wrapper layer; downstream code
should use the owner theorem directly or prove the needed statement in place.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryCrystalSouriauWeyl

open InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge
open InfoGeometry.Canonical.WeylCharacterEquivalence

/--
Combined binary-crystal / Souriau-Weyl packet.

The binary crystal provides the symbolic address-space, shift parity, and
Bloch readout.  The Souriau/Weyl packet is stored as data for downstream code
that wants to invoke the owner theorems directly.
-/
@[rep_depth transport]
structure BinaryCrystalSouriauWeylBridge
    (G : Type*) [Group G] [MulAction G BinaryLattice] (𝔤 : Type*) where
  crystal : BinaryCrystalWeylBlochPacket G
  souriauWeyl : SouriauWeylPartitionPacket 𝔤

namespace BinaryCrystalSouriauWeylBridge

variable {G : Type*} [Group G] [MulAction G BinaryLattice] {𝔤 : Type*}
variable (B : BinaryCrystalSouriauWeylBridge G 𝔤)

/-- The binary crystal side retains the depth-parity readout. -/
@[rep_depth transport]
theorem binaryCrystal_ownerTarget :
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

end BinaryCrystalSouriauWeylBridge

end InfoGeometry.Canonical.BinaryCrystalSouriauWeyl
