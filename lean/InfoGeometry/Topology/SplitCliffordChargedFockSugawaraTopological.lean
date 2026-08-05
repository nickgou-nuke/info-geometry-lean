import Mathlib
import InfoGeometry.Topology.SplitCliffordChargedFockWitnessTopological

/-!
# Topological packet for the charged-Fock Sugawara output

The concrete charged-Fock witness already supplies the canonical
`CurrentSugawaraMorphism`.  This owner packages the dependent family of
those morphisms and exposes its two defining generator readouts.  The
topological statement is deliberately discrete; it does not claim a
continuous field of operators between differently indexed Fock spaces.
-/

namespace InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Topology.SplitCliffordChargedFockWitnessTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Sugawara morphism attached to the concrete charged-Fock witness. -/
def representedChargedFockSugawaraMorphism (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  (representedChargedFockWitness (𝕜 := 𝕜) α).toCurrentSugawaraMorphism

@[simp] theorem representedChargedFockSugawaraMorphism_heisenberg (α : 𝕜) :
    (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).heisenberg =
      (representedChargedFockWitness (𝕜 := 𝕜) α).toCurrentHeisenbergRep := by
  rfl

theorem representedChargedFockSugawaraMorphism_central (α : 𝕜) :
    (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).virasoro
        (VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).central_apply

theorem representedChargedFockSugawaraMorphism_lgen (α : 𝕜) (n : Int) :
      (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).virasoro
        (VirasoroAlgebra.lgen 𝕜 n) =
      ((representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).heisenberg).sugawaraStressMode n := by
  exact (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).lgen_apply n

/-- Dependent packet of the concrete charged-Fock Sugawara morphisms. -/
abbrev ChargedFockSugawaraPacket (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  Σ α : 𝕜,
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)

instance chargedFockSugawaraPacketTopologicalSpace :
    TopologicalSpace (ChargedFockSugawaraPacket 𝕜) := ⊥

instance chargedFockSugawaraPacketDiscreteTopology :
    DiscreteTopology (ChargedFockSugawaraPacket 𝕜) := ⟨rfl⟩

def representedChargedFockSugawaraPacket (α : 𝕜) :
    ChargedFockSugawaraPacket 𝕜 :=
  ⟨α, representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α⟩

@[simp] theorem representedChargedFockSugawaraPacket_fst (α : 𝕜) :
    (representedChargedFockSugawaraPacket (𝕜 := 𝕜) α).1 = α := by
  rfl

@[simp] theorem representedChargedFockSugawaraPacket_snd (α : 𝕜) :
    (representedChargedFockSugawaraPacket (𝕜 := 𝕜) α).2 =
      representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α := by
  rfl

theorem continuous_representedChargedFockSugawaraPacket :
    Continuous (representedChargedFockSugawaraPacket (𝕜 := 𝕜)) := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_representedChargedFockSugawaraPacket :
    IsLocallyConstant (representedChargedFockSugawaraPacket (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete
    (f := representedChargedFockSugawaraPacket (𝕜 := 𝕜))

end
end InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological
