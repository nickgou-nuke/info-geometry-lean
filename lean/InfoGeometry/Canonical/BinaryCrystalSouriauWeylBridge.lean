import Mathlib
import InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge
import InfoGeometry.Canonical.WeylCharacterEquivalence

/-!
# InfoGeometry.Canonical.BinaryCrystalSouriauWeylBridge

Specialization bridge for the binary-fractal crystal and Souriau/Weyl
partition surface.

This file does not prove a new Weyl character formula or a new Euler-product
identity.  It bundles the repo-owned binary crystal packet with the repo-owned
Souriau/Weyl partition packet and re-exports their theorem-safe readouts.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryCrystalSouriauWeylBridge

open InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge
open InfoGeometry.Canonical.WeylCharacterEquivalence

/--
Combined binary-crystal / Souriau-Weyl packet.

The binary crystal provides the symbolic address-space, shift parity, and
Bloch readout.  The Souriau/Weyl packet provides the partition-function,
denominator, and parity-trace readouts.
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
    BinaryCrystalWeylBlochOwnerTarget :=
  binaryCrystalWeylBlochOwnerTarget

/-- The Souriau partition function is its own character readout. -/
@[rep_depth transport]
theorem partitionFunction_is_souriau_character :
    B.souriauWeyl.representation.partitionFunction B.souriauWeyl.beta =
      B.souriauWeyl.representation.character
        (B.souriauWeyl.representation.thermalElement B.souriauWeyl.beta) := by
  exact SouriauWeylPartitionPacket.partitionFunction_is_souriau_character B.souriauWeyl

/-- The Weyl denominator readout matches the prime Euler product readout. -/
@[rep_depth transport]
theorem denominator_is_prime_euler_product :
    B.souriauWeyl.denominatorBridge.weylDenominator =
      B.souriauWeyl.denominatorBridge.primeEulerProduct :=
  SouriauWeylPartitionPacket.denominator_is_prime_euler_product B.souriauWeyl

/-- The parity-trace readback is available on the stored squarefree lane. -/
@[rep_depth transport]
theorem parity_trace_readback
    (n : ℕ) (h : B.souriauWeyl.parityWitness.squareFree n) :
    B.souriauWeyl.parityWitness.signature
        (B.souriauWeyl.parityWitness.squareFreeToWeyl n h) =
      mobiusCoefficient n :=
  SouriauWeylPartitionPacket.parity_trace_witness B.souriauWeyl n h

end BinaryCrystalSouriauWeylBridge

end InfoGeometry.Canonical.BinaryCrystalSouriauWeylBridge
