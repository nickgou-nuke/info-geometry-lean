import InfoGeometry.Algebra.Zorn.G2CorrectedTComplementCard

/-!
# The index-two PC partition of the unipotent carrier

The zeroth PC bit gives a structural two-coset partition.  The proof uses
normal-form multiplication and injectivity, not enumeration of the group.
-/

namespace InfoGeometry.Algebra.Zorn.G2CorrectedTComplementPartition

open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.Algebra.Zorn.G2CorrectedTComplementCard
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def correctedTLeftCoset : Set SplitOctF2Aut :=
  {x | ∃ h ∈ correctedTComplementSubgroup,
    G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h = x}

theorem correctedTLeftCoset_disjoint_complement :
    Disjoint (correctedTComplementSubgroup : Set SplitOctF2Aut)
      correctedTLeftCoset := by
  rw [Set.disjoint_left]
  intro x hxC hxT
  rcases hxT with ⟨h, hh, hxh⟩
  have hh' : h ∈ zeroBitPCSubgroup := by
    rw [zeroBitPCSubgroup_eq_correctedTComplementSubgroup]
    exact hh
  rcases hh' with ⟨f, hf, hfh⟩
  have hxC' : x ∈ zeroBitPCSubgroup := by
    rw [zeroBitPCSubgroup_eq_correctedTComplementSubgroup]
    exact hxC
  rcases hxC' with ⟨e, he, hxe⟩
  have hword :
      G2TwoSylowSubgroup.pcWord correctedTRankOneExponent *
          G2TwoSylowSubgroup.pcWord f =
        G2TwoSylowSubgroup.pcWord e := by
    calc
      G2TwoSylowSubgroup.pcWord correctedTRankOneExponent *
          G2TwoSylowSubgroup.pcWord f =
          G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h := by
            rw [hfh]
      _ = x := hxh
      _ = G2TwoSylowSubgroup.pcWord e := hxe.symm
  have hexp : pcCombine correctedTRankOneExponent f = e := by
    apply pcWord_injective
    rw [pcWord_mul_pcWord] at hword
    exact hword
  have hzero := congrArg (fun q : PCExponent => q 0) hexp
  have : (true : Bool) = false := by
    simpa [pcCombine_apply_zero, correctedTRankOneExponent, hf, he] using hzero
  cases this

theorem unipotent_mem_complement_or_correctedTLeftCoset
    {b : SplitOctF2Aut} (hb : b ∈ unipotentSubgroup) :
    b ∈ correctedTComplementSubgroup ∨ b ∈ correctedTLeftCoset := by
  rcases correctedT_borel_split b hb with h | ⟨h, hh, heq⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hh, heq.symm⟩

theorem unipotentSubgroup_subset_complement_union_correctedT :
    (unipotentSubgroup : Set SplitOctF2Aut) ⊆
      (correctedTComplementSubgroup : Set SplitOctF2Aut) ∪
        correctedTLeftCoset := by
  intro b hb
  rcases unipotent_mem_complement_or_correctedTLeftCoset hb with h | h
  · exact Or.inl h
  · exact Or.inr h

noncomputable def correctedTLeftCosetEquiv :
    correctedTComplementSubgroup ≃
      {x : SplitOctF2Aut // x ∈ correctedTLeftCoset} where
  toFun h := ⟨G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h.1,
    ⟨h.1, h.2, rfl⟩⟩
  invFun x :=
    ⟨(G2TwoSylowSubgroup.pcWord correctedTRankOneExponent)⁻¹ * x.1, by
      rcases x.2 with ⟨h, hh, heq⟩
      have : (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent)⁻¹ * x.1 = h := by
        rw [← heq]
        simp [mul_assoc]
      rw [this]
      exact hh⟩
  left_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    rcases x.2 with ⟨h, hh, heq⟩
    change G2TwoSylowSubgroup.pcWord correctedTRankOneExponent *
      ((G2TwoSylowSubgroup.pcWord correctedTRankOneExponent)⁻¹ * x.1) = x.1
    group

theorem correctedTLeftCoset_card :
    Nat.card {x : SplitOctF2Aut // x ∈ correctedTLeftCoset} = 32 := by
  calc
    Nat.card {x : SplitOctF2Aut // x ∈ correctedTLeftCoset} =
        Nat.card correctedTComplementSubgroup :=
      Nat.card_congr correctedTLeftCosetEquiv.symm
    _ = 32 := correctedTComplementSubgroup_card

theorem unipotentSubgroup_eq_complement_union_correctedT :
    (unipotentSubgroup : Set SplitOctF2Aut) =
      (correctedTComplementSubgroup : Set SplitOctF2Aut) ∪
        correctedTLeftCoset := by
  apply Set.Subset.antisymm
  · exact unipotentSubgroup_subset_complement_union_correctedT
  · intro x hx
    rcases hx with hx | hx
    · exact correctedTComplementSubgroup_le_unipotentSubgroup hx
    · rcases hx with ⟨h, hh, heq⟩
      rw [← heq]
      apply unipotentSubgroup.mul_mem
      · exact ⟨correctedTRankOneExponent, rfl⟩
      · exact correctedTComplementSubgroup_le_unipotentSubgroup hh

end InfoGeometry.Algebra.Zorn.G2CorrectedTComplementPartition
