import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.SplitCliffordHeisenbergTopological

/-!
# Concrete charged-Fock split-Clifford Heisenberg property

The source-current owner already proves truncation and the endomorphism-valued
Heisenberg commutator for the represented charged-Fock current family.  This
owner packages those proofs into the canonical property structure and then
places the dependent family of witnesses in a discrete topological packet.
No existential choice or additional current law is introduced.
-/

namespace InfoGeometry.Topology.SplitCliffordChargedFockTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The concrete property carried by the represented charged-Fock current. -/
def representedChargedFockData (α : 𝕜) :
    SplitCliffordHeisenbergWitness 𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α) where
  J := representedChargedFockJ 𝕜 α
  trunc := representedChargedFockJ_trunc 𝕜 α
  comm := representedChargedFockJ_wick 𝕜 α

@[simp] theorem representedChargedFockData_J (α : 𝕜) :
    (representedChargedFockData (𝕜 := 𝕜) α).J =
      representedChargedFockJ 𝕜 α := by
  rfl

theorem representedChargedFockData_trunc (α : 𝕜) :
    ∀ v, ∀ᶠ n : Int in Filter.atTop,
      (representedChargedFockData (𝕜 := 𝕜) α).J n v = 0 := by
  exact representedChargedFockJ_trunc 𝕜 α

theorem representedChargedFockData_comm (α : 𝕜) (m n : Int) :
    ((representedChargedFockData (𝕜 := 𝕜) α).J m).commutator
        ((representedChargedFockData (𝕜 := 𝕜) α).J n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0 := by
  exact representedChargedFockJ_wick 𝕜 α m n

/-- Dependent packet of all concrete charged-Fock witnesses. -/
abbrev ChargedFockDataPacket (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  Σ α : 𝕜,
    SplitCliffordHeisenbergWitness 𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α)

instance chargedFockDataPacketTopologicalSpace :
    TopologicalSpace (ChargedFockDataPacket 𝕜) := ⊥

instance chargedFockDataPacketDiscreteTopology :
    DiscreteTopology (ChargedFockDataPacket 𝕜) := ⟨rfl⟩

/-- The concrete property family as a topological packet-valued readout. -/
def representedChargedFockDataPacket (α : 𝕜) :
    ChargedFockDataPacket 𝕜 :=
  ⟨α, representedChargedFockData (𝕜 := 𝕜) α⟩

@[simp] theorem representedChargedFockDataPacket_fst (α : 𝕜) :
    (representedChargedFockDataPacket (𝕜 := 𝕜) α).1 = α := by
  rfl

@[simp] theorem representedChargedFockDataPacket_snd (α : 𝕜) :
    (representedChargedFockDataPacket (𝕜 := 𝕜) α).2 =
      representedChargedFockData (𝕜 := 𝕜) α := by
  rfl

theorem continuous_representedChargedFockDataPacket :
    Continuous (representedChargedFockDataPacket (𝕜 := 𝕜)) := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_representedChargedFockDataPacket :
    IsLocallyConstant (representedChargedFockDataPacket (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete
    (f := representedChargedFockDataPacket (𝕜 := 𝕜))

end
end InfoGeometry.Topology.SplitCliffordChargedFockTopological
