import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalFormInverse
import InfoGeometry.Algebra.Zorn.G2TwoPCGroup
import Mathlib.GroupTheory.Sylow

namespace InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G]
abbrev E := Fin 6 → Bool

theorem range_is_subgroup
    (word : E → G)
    (h_one : word (fun _ : Fin 6 => false) = 1)
    (h_mul : ∀ e f, word e * word f ∈ Set.range word)
    (h_inv : ∀ e, (word e)⁻¹ ∈ Set.range word) :
    ∃ H : Subgroup G, H.carrier = Set.range word := by
  let H : Subgroup G :=
    { carrier := Set.range word
      one_mem' := by
        rw [← h_one]
        exact ⟨fun _ => false, rfl⟩
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨e, rfl⟩
        rcases hb with ⟨f, rfl⟩
        exact h_mul e f
      inv_mem' := by
        intro a ha
        rcases ha with ⟨e, rfl⟩
        exact h_inv e }
  exact ⟨H, rfl⟩

theorem range_card_of_injective
    (word : E → G)
    (hinj : Function.Injective word) :
    Nat.card (Set.range word) = 64 := by
  exact (Nat.card_range_of_injective hinj).trans (by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
    norm_num)

theorem range_subgroup_card
    (word : E → G)
    (h_one : word (fun _ : Fin 6 => false) = 1)
    (h_mul : ∀ e f, word e * word f ∈ Set.range word)
    (h_inv : ∀ e, (word e)⁻¹ ∈ Set.range word)
    (hinj : Function.Injective word) :
    ∃ H : Subgroup G, H.carrier = Set.range word ∧ Nat.card H = 64 := by
  rcases range_is_subgroup word h_one h_mul h_inv with ⟨H, hH⟩
  refine ⟨H, hH, ?_⟩
  change Nat.card {x // x ∈ H.carrier} = 64
  rw [hH]
  exact range_card_of_injective word hinj

end Generic

/-- THEOREM: The 64-element polycyclic image of `pcWord` inside `SplitOctF2Aut`
has exact cardinality 64. -/
theorem pcWord_range_card_eq_64 :
    Nat.card (Set.range G2TwoSylowSubgroup.pcWord) = 64 :=
  range_card_of_injective G2TwoSylowSubgroup.pcWord
    _root_.InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport.pcWord_injective_concrete

/-- THEOREM: The Sylow 2-subgroup contains at least 64 distinct elements. -/
theorem sylowTwoSubgroup_card_ge_64 :
    64 ≤ Nat.card G2TwoSylowSubgroup.sylowTwoSubgroup :=
  _root_.InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport.sylowTwoSubgroup_card_ge_64_concrete

/-- THEOREM: Group inverse of a concrete polycyclic word in `SplitOctF2Aut`. -/
theorem pcWord_inv (e : PCExponent) :
    (G2TwoSylowSubgroup.pcWord e)⁻¹ = G2TwoSylowSubgroup.pcWord (pcInverse e) := by
  apply inv_eq_of_mul_eq_one_left
  rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
  rw [pcCombine_left_inverse]
  exact pcWord_zero_eq_one

def pcCommutatorExponent (e f : PCExponent) : PCExponent :=
  pcCombine (pcCombine (pcCombine e f) (pcInverse e)) (pcInverse f)

theorem pcWord_commutator (e f : PCExponent) :
    G2TwoSylowSubgroup.pcWord e * G2TwoSylowSubgroup.pcWord f *
        (G2TwoSylowSubgroup.pcWord e)⁻¹ *
          (G2TwoSylowSubgroup.pcWord f)⁻¹ =
      G2TwoSylowSubgroup.pcWord (pcCommutatorExponent e f) := by
  rw [pcWord_inv, pcWord_inv]
  calc
    (G2TwoSylowSubgroup.pcWord e * G2TwoSylowSubgroup.pcWord f) *
        G2TwoSylowSubgroup.pcWord (pcInverse e) *
          G2TwoSylowSubgroup.pcWord (pcInverse f) =
        G2TwoSylowSubgroup.pcWord (pcCombine e f) *
          G2TwoSylowSubgroup.pcWord (pcInverse e) *
            G2TwoSylowSubgroup.pcWord (pcInverse f) := by
              rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
    _ = G2TwoSylowSubgroup.pcWord (pcCombine (pcCombine e f) (pcInverse e)) *
          G2TwoSylowSubgroup.pcWord (pcInverse f) := by
              rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
    _ = G2TwoSylowSubgroup.pcWord (pcCommutatorExponent e f) := by
              rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
              rfl

/-- THEOREM: The concrete 64-element unipotent 2-subgroup of `SplitOctF2Aut`.
The Sylow property requires the ambient carrier cardinality. -/
def unipotentSubgroup : Subgroup SplitOctF2Aut where
  carrier := Set.range G2TwoSylowSubgroup.pcWord
  one_mem' := ⟨zeroPC, pcWord_zero_eq_one⟩
  mul_mem' := by
    rintro _ _ ⟨e, rfl⟩ ⟨f, rfl⟩
    rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
    exact ⟨pcCombine e f, rfl⟩
  inv_mem' := by
    rintro _ ⟨e, rfl⟩
    rw [pcWord_inv]
    exact ⟨pcInverse e, rfl⟩

theorem sylowTwoSubgroup_eq_unipotentSubgroup :
    G2TwoSylowSubgroup.sylowTwoSubgroup = unipotentSubgroup := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    change x ∈ Set.range G2TwoSylowSubgroup.pcWord
    rcases hx with ⟨i, rfl⟩
    exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range i
  · intro x hx
    rcases hx with ⟨e, rfl⟩
    exact G2TwoSylowSubgroup.pcWord_mem_sylow e

/-- THEOREM: Exact cardinality 64 of the concrete unipotent subgroup U₆ ⊂ G₂(2). -/
theorem unipotentSubgroup_card : Nat.card unipotentSubgroup = 64 := by
  have hc : Nat.card {x // x ∈ unipotentSubgroup.carrier} = 64 := by
    change Nat.card (Set.range G2TwoSylowSubgroup.pcWord) = 64
    exact pcWord_range_card_eq_64
  exact hc

theorem unipotentSubgroup_isPGroup : IsPGroup 2 unipotentSubgroup := by
  apply @IsPGroup.of_card _ _ _ 6
  rw [unipotentSubgroup_card]
  rfl

theorem unipotentSubgroup_isSylow_of_ambient_card
    (hG : Nat.card SplitOctF2Aut = 12096) :
    ∃ P : Sylow 2 SplitOctF2Aut, (P : Subgroup SplitOctF2Aut) = unipotentSubgroup := by
  have hindex : unipotentSubgroup.index = 189 := by
    have h := unipotentSubgroup.card_mul_index
    rw [unipotentSubgroup_card, hG] at h
    omega
  have hnot : ¬ 2 ∣ unipotentSubgroup.index := by
    rw [hindex]
    norm_num
  exact ⟨unipotentSubgroup_isPGroup.toSylow hnot,
    IsPGroup.toSylow_coe unipotentSubgroup_isPGroup hnot⟩

/-- MAIN THEOREM (Exact Group Isomorphism):
The abstract polycyclic group `PCExponent` (with multiplication `pcCombine`)
is strictly isomorphic to the concrete subgroup `unipotentSubgroup`.
-/
noncomputable def pcWordMulEquiv : PCExponent ≃* unipotentSubgroup where
  toFun e := ⟨G2TwoSylowSubgroup.pcWord e, ⟨e, rfl⟩⟩
  invFun x := Classical.choose x.2
  left_inv e := by
    have h := Classical.choose_spec (⟨G2TwoSylowSubgroup.pcWord e, ⟨e, rfl⟩⟩ : unipotentSubgroup).2
    apply _root_.InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport.pcWord_injective_concrete
    exact h
  right_inv x := by
    ext
    exact Classical.choose_spec x.2
  map_mul' e f := by
    ext
    change G2TwoSylowSubgroup.pcWord (pcCombine e f) =
      G2TwoSylowSubgroup.pcWord e * G2TwoSylowSubgroup.pcWord f
    rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]

end InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
