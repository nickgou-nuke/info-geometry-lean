import Mathlib
import InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.SplitCliffordHeisenbergTopological

/-!
# Concrete charged-Fock split-Clifford Heisenberg witness

The source-current owner already proves truncation and the endomorphism-valued
Heisenberg commutator for the represented charged-Fock current family.  This
owner packages those proofs into the canonical witness structure and then
places the dependent family of witnesses in a discrete topological packet.
No existential choice or additional current law is introduced.
-/

namespace InfoGeometry.Topology.SplitCliffordChargedFockWitnessTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The concrete witness carried by the represented charged-Fock current. -/
def representedChargedFockWitness (α : 𝕜) :
    SplitCliffordHeisenbergWitness 𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α) where
  J := representedChargedFockJ 𝕜 α
  trunc := representedChargedFockJ_trunc 𝕜 α
  comm := representedChargedFockJ_wick 𝕜 α

@[simp] theorem representedChargedFockWitness_J (α : 𝕜) :
    (representedChargedFockWitness (𝕜 := 𝕜) α).J =
      representedChargedFockJ 𝕜 α := by
  rfl

theorem representedChargedFockWitness_trunc (α : 𝕜) :
    ∀ v, ∀ᶠ n : Int in Filter.atTop,
      (representedChargedFockWitness (𝕜 := 𝕜) α).J n v = 0 := by
  exact representedChargedFockJ_trunc 𝕜 α

theorem representedChargedFockWitness_comm (α : 𝕜) (m n : Int) :
    ((representedChargedFockWitness (𝕜 := 𝕜) α).J m).commutator
        ((representedChargedFockWitness (𝕜 := 𝕜) α).J n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0 := by
  exact representedChargedFockJ_wick 𝕜 α m n

/-- Dependent packet of all concrete charged-Fock witnesses. -/
abbrev ChargedFockWitnessPacket (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  Σ α : 𝕜,
    SplitCliffordHeisenbergWitness 𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α)

instance chargedFockWitnessPacketTopologicalSpace :
    TopologicalSpace (ChargedFockWitnessPacket 𝕜) := ⊥

instance chargedFockWitnessPacketDiscreteTopology :
    DiscreteTopology (ChargedFockWitnessPacket 𝕜) := ⟨rfl⟩

/-- The concrete witness family as a topological packet-valued readout. -/
def representedChargedFockWitnessPacket (α : 𝕜) :
    ChargedFockWitnessPacket 𝕜 :=
  ⟨α, representedChargedFockWitness (𝕜 := 𝕜) α⟩

@[simp] theorem representedChargedFockWitnessPacket_fst (α : 𝕜) :
    (representedChargedFockWitnessPacket (𝕜 := 𝕜) α).1 = α := by
  rfl

@[simp] theorem representedChargedFockWitnessPacket_snd (α : 𝕜) :
    (representedChargedFockWitnessPacket (𝕜 := 𝕜) α).2 =
      representedChargedFockWitness (𝕜 := 𝕜) α := by
  rfl

theorem continuous_representedChargedFockWitnessPacket :
    Continuous (representedChargedFockWitnessPacket (𝕜 := 𝕜)) := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_representedChargedFockWitnessPacket :
    IsLocallyConstant (representedChargedFockWitnessPacket (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete
    (f := representedChargedFockWitnessPacket (𝕜 := 𝕜))

end
end InfoGeometry.Topology.SplitCliffordChargedFockWitnessTopological
