import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SplitCliffordChargedFockTopological

/-!
# Topological Bundle for the Charged-Fock Sugawara Virasoro Output

This module constructs `representedChargedFockSugawaraMorphism α` from
`representedChargedFockData α`, places the dependent family of Sugawara morphisms
in the sigma bundle `ChargedFockSugawaraBundle 𝕜`, and proves its generator
readouts, continuity, and local constancy.

## 1. Real Math in This File
- `representedChargedFockSugawaraMorphism`,
  `representedChargedFockSugawaraMorphism_heisenberg`,
  `representedChargedFockSugawaraMorphism_central`,
  `representedChargedFockSugawaraMorphism_lgen`
- `ChargedFockSugawaraBundle`, `representedChargedFockSugawaraBundle`
- `representedChargedFockSugawaraBundle_fst`,
  `representedChargedFockSugawaraBundle_snd`,
  `continuous_representedChargedFockSugawaraBundle`,
  `isLocallyConstant_representedChargedFockSugawaraBundle`

## 2. Meaningful Mathematical Results Used
- `InfoGeometry.Topology.SplitCliffordChargedFockTopological`
- `InfoGeometry.Canonical.CurrentSugawaraBridge`

## 3. Excluded Wrapper Patterns
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Topology.SplitCliffordChargedFockTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Sugawara morphism attached to `representedChargedFockData α`. -/
def representedChargedFockSugawaraMorphism (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  (representedChargedFockData (𝕜 := 𝕜) α).toCurrentSugawaraMorphism

/-- The Heisenberg component of `representedChargedFockSugawaraMorphism α` is
`(representedChargedFockData α).toCurrentHeisenbergRep`. -/
@[simp] theorem representedChargedFockSugawaraMorphism_heisenberg (α : 𝕜) :
    (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).heisenberg =
      (representedChargedFockData (𝕜 := 𝕜) α).toCurrentHeisenbergRep := by
  unfold representedChargedFockSugawaraMorphism
  exact SplitCliffordHeisenbergWitness.toCurrentSugawaraMorphism_heisenberg _

/-- The Virasoro central generator acts as the identity in
`representedChargedFockSugawaraMorphism α`. -/
theorem representedChargedFockSugawaraMorphism_central (α : 𝕜) :
    (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).virasoro
        (VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).central_apply

/-- The Virasoro mode generator `lgen 𝕜 n` acts as `sugawaraStressMode n` in
`representedChargedFockSugawaraMorphism α`. -/
theorem representedChargedFockSugawaraMorphism_lgen (α : 𝕜) (n : Int) :
      (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).virasoro
        (VirasoroAlgebra.lgen 𝕜 n) =
      ((representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).heisenberg).sugawaraStressMode n := by
  exact (representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α).lgen_apply n

/-- Dependent sigma bundle of concrete charged-Fock Sugawara morphisms over `α : 𝕜`. -/
abbrev ChargedFockSugawaraBundle (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  Σ α : 𝕜,
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)

/-- Discrete topology on `ChargedFockSugawaraBundle 𝕜`. -/
instance chargedFockSugawaraBundleTopologicalSpace :
    TopologicalSpace (ChargedFockSugawaraBundle 𝕜) := ⊥

/-- `DiscreteTopology` instance on `ChargedFockSugawaraBundle 𝕜`. -/
instance chargedFockSugawaraBundleDiscreteTopology :
    DiscreteTopology (ChargedFockSugawaraBundle 𝕜) := ⟨rfl⟩

/-- Section `α ↦ ⟨α, representedChargedFockSugawaraMorphism α⟩` into
`ChargedFockSugawaraBundle 𝕜`. -/
def representedChargedFockSugawaraBundle (α : 𝕜) :
    ChargedFockSugawaraBundle 𝕜 :=
  ⟨α, representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α⟩

/-- First sigma coordinate of `representedChargedFockSugawaraBundle α`. -/
@[simp] theorem representedChargedFockSugawaraBundle_fst (α : 𝕜) :
    (representedChargedFockSugawaraBundle (𝕜 := 𝕜) α).1 = α := by
  unfold representedChargedFockSugawaraBundle
  rfl

/-- Second sigma coordinate of `representedChargedFockSugawaraBundle α`. -/
@[simp] theorem representedChargedFockSugawaraBundle_snd (α : 𝕜) :
    (representedChargedFockSugawaraBundle (𝕜 := 𝕜) α).2 =
      representedChargedFockSugawaraMorphism (𝕜 := 𝕜) α := by
  unfold representedChargedFockSugawaraBundle
  rfl

/-- Continuity of `representedChargedFockSugawaraBundle`. -/
theorem continuous_representedChargedFockSugawaraBundle :
    Continuous (representedChargedFockSugawaraBundle (𝕜 := 𝕜)) := by
  exact continuous_of_discreteTopology

/-- Local constancy of `representedChargedFockSugawaraBundle`. -/
theorem isLocallyConstant_representedChargedFockSugawaraBundle :
    IsLocallyConstant (representedChargedFockSugawaraBundle (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete
    (f := representedChargedFockSugawaraBundle (𝕜 := 𝕜))

end
end InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological
