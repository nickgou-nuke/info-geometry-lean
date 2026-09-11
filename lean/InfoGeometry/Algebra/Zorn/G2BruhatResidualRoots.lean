import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots
import InfoGeometry.Algebra.Zorn.G2ChevalleyPoincareCombinatorics
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem

/-!
# Root-labelled residual generators for the concrete finite `G₂(2)` carrier

This file is only the root-label bridge.  The six concrete generators and
their kernel-checked relations are owned by `G2SteinbergPositiveRoots`; this
owner gives them the abstract positive-root names without duplicating those
certificates.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidual

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem

private def positiveRootIndex : G2PositiveRoot → Fin 6
  | .alpha => 0
  | .beta => 1
  | .alpha_add_beta => 2
  | .two_alpha_beta => 3
  | .three_alpha_beta => 4
  | .three_alpha_two_beta => 5

/-- The concrete root-group generator attached to a positive `G₂` root. -/
noncomputable def positiveRootGenerator
    (α : G2PositiveRoot) (t : Bool) : SplitOctF2Aut :=
  positiveRootAction (positiveRootIndex α) t

theorem positiveRootGenerator_sq (α : G2PositiveRoot) :
    positiveRootGenerator α true * positiveRootGenerator α true = 1 := by
  cases α <;> simp [positiveRootGenerator, positiveRootIndex,
    positiveRootAction, positiveRootPacket_sq]

theorem positiveRootGenerator_false (α : G2PositiveRoot) :
    positiveRootGenerator α false = 1 := by
  cases α <;> rfl

theorem positiveRootGenerator_ne_one (α : G2PositiveRoot) :
    positiveRootGenerator α true ≠ (1 : SplitOctF2Aut) := by
  cases α <;>
    simp [positiveRootGenerator, positiveRootIndex, positiveRootAction,
      positiveRootPacket_ne_one]

theorem positiveRootGenerator_mem_positiveRootSubgroup
    (α : G2PositiveRoot) (t : Bool) :
    positiveRootGenerator α t ∈ positiveRootSubgroup := by
  cases t
  · rw [positiveRootGenerator_false]
    exact positiveRootSubgroup.one_mem
  · exact positiveRootAction_mem_positiveRootSubgroup
      (positiveRootIndex α) true

/-! This is the exact reduction used by the later concrete alignment owner.
It records that a proved six-generator correspondence is sufficient for the
two closure subgroups to coincide; no correspondence is assumed here. -/

theorem positiveRootSubgroup_eq_pcSubgroup_of_generator_equivalence
    (σ : Fin 6 ≃ Fin 6)
    (hσ : ∀ i : Fin 6, positiveRootPacket i = pcGenerator (σ i)) :
    positiveRootSubgroup = pcSubgroup := by
  apply le_antisymm
  · rw [positiveRootSubgroup]
    rw [Subgroup.closure_le]
    rintro g ⟨i, rfl⟩
    rw [hσ i]
    exact Subgroup.subset_closure ⟨σ i, rfl⟩
  · rw [pcSubgroup]
    rw [Subgroup.closure_le]
    rintro g ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := σ.surjective i
    rw [← hσ j]
    exact positiveRootPacket_mem_subgroup j

/-! A separate root-labelled packet for the order-64 PC/Borel carrier.
This is intentionally not identified with `positiveRootPacket`: the latter
belongs to the distinct root-system carrier. -/

noncomputable def pcPositiveRootPacket : G2PositiveRoot → SplitOctF2Aut :=
  fun α => pcGenerator (positiveRootIndex α)

theorem pcPositiveRootPacket_mem_pcSubgroup (α : G2PositiveRoot) :
    pcPositiveRootPacket α ∈ pcSubgroup := by
  exact pcGenerator_mem_pcSubgroup (positiveRootIndex α)

theorem pcPositiveRootPacket_range_closure_eq_pcSubgroup :
    Subgroup.closure (Set.range pcPositiveRootPacket) = pcSubgroup := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with ⟨α, rfl⟩
    exact pcPositiveRootPacket_mem_pcSubgroup α
  · rw [pcSubgroup, Subgroup.closure_le]
    intro g hg
    rcases hg with ⟨i, rfl⟩
    let α : G2PositiveRoot := match i with
      | 0 => .alpha
      | 1 => .beta
      | 2 => .alpha_add_beta
      | 3 => .two_alpha_beta
      | 4 => .three_alpha_beta
      | 5 => .three_alpha_two_beta
    have hα : positiveRootIndex α = i := by
      fin_cases i <;> rfl
    refine Subgroup.subset_closure ?_
    refine ⟨α, ?_⟩
    simp [pcPositiveRootPacket, hα]

/-! The six roots selected by the concrete PC Borel.  This is the corrected
positive system; it is distinct from the auxiliary `positiveRootPacket`
carrier above. -/

def pcBorelRootIndex : Fin 6 → G2Root
  | 0 => (RootLength.Short, 1)
  | 1 => (RootLength.Short, 2)
  | 2 => (RootLength.Long, 2)
  | 3 => (RootLength.Short, 3)
  | 4 => (RootLength.Long, 3)
  | 5 => (RootLength.Long, 4)

theorem pcBorelRootIndex_injective :
    Function.Injective pcBorelRootIndex := by
  decide

end InfoGeometry.Algebra.Zorn.G2BruhatResidual
