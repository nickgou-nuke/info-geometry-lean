import InfoGeometry.Algebra.Zorn.G2NativeBruhatRootSubgroupSystem
import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2NativeRootProductImage

open InfoGeometry.Algebra.Zorn.G2NativeBruhatRootSubgroupSystem
open InfoGeometry.Algebra.Zorn.G2RootSubgroup
open InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Unipotent
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

theorem xRoot_short_zero_true_eq_positiveRootPacket_zero :
    xRoot (RootLength.Short, 0) true = positiveRootPacket 0 := by
  rfl

theorem xRoot_short_one_three_commutator_eq_short_two :
    automorphismCommutator
        (xRoot (RootLength.Short, 1) true)
        (xRoot (RootLength.Short, 3) true) =
      xRoot (RootLength.Short, 2) true := by
  have hc : cAction (RootLength.Short, 0) = (RootLength.Short, 1) := by
    rfl
  have hc' : cAction (RootLength.Short, 2) = (RootLength.Short, 3) := by
    rfl
  have hconj (a b : SplitOctF2Aut) :
      automorphismCommutator (c * a * c⁻¹) (c * b * c⁻¹) =
        c * automorphismCommutator a b * c⁻¹ := by
    simp [automorphismCommutator, mul_assoc]
  rw [← hc, ← hc', ← c_xRoot_c, ← c_xRoot_c, hconj]
  rw [native_root_commutator_short_0_2]
  rw [c_xRoot_c]
  rfl

theorem rootSubgroup_short_two_le_short_one_short_three_closure :
    rootSubgroup (RootLength.Short, 2) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Short, 3) : Set SplitOctF2Aut)) := by
  intro x hx
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective (RootLength.Short, 2) ⟨x, hx⟩
  cases t with
  | false =>
      have hx0 : xRoot (RootLength.Short, 2) false = x :=
        congrArg Subtype.val ht
      rw [← hx0, native_root_zero]
      exact Subgroup.one_mem _
  | true =>
      have h1 : xRoot (RootLength.Short, 1) true ∈
          Subgroup.closure
            ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
              (rootSubgroup (RootLength.Short, 3) : Set SplitOctF2Aut)) :=
        Subgroup.subset_closure (Or.inl
          (native_root_mem (RootLength.Short, 1) true))
      have h3 : xRoot (RootLength.Short, 3) true ∈
          Subgroup.closure
            ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
              (rootSubgroup (RootLength.Short, 3) : Set SplitOctF2Aut)) :=
        Subgroup.subset_closure (Or.inr
          (native_root_mem (RootLength.Short, 3) true))
      let H : Subgroup SplitOctF2Aut := Subgroup.closure
        ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Short, 3) : Set SplitOctF2Aut))
      have hc := H.mul_mem (H.mul_mem h1 h3) (H.inv_mem h1)
      have hc := H.mul_mem hc (H.inv_mem h3)
      have hx2 : xRoot (RootLength.Short, 2) true = x :=
        congrArg Subtype.val ht
      rw [← hx2]
      have hcomm : automorphismCommutator
          (xRoot (RootLength.Short, 1) true)
          (xRoot (RootLength.Short, 3) true) ∈ H := by
        simpa [automorphismCommutator, H, mul_assoc] using hc
      rw [xRoot_short_one_three_commutator_eq_short_two] at hcomm
      exact hcomm

theorem xRoot_short_two_four_commutator_eq_short_three :
    automorphismCommutator
        (xRoot (RootLength.Short, 2) true)
        (xRoot (RootLength.Short, 4) true) =
      xRoot (RootLength.Short, 3) true := by
  have hc : cAction (RootLength.Short, 1) = (RootLength.Short, 2) := by
    rfl
  have hc' : cAction (RootLength.Short, 3) = (RootLength.Short, 4) := by
    rfl
  have hconj (a b : SplitOctF2Aut) :
      automorphismCommutator (c * a * c⁻¹) (c * b * c⁻¹) =
        c * automorphismCommutator a b * c⁻¹ := by
    simp [automorphismCommutator, mul_assoc]
  rw [← hc, ← hc', ← c_xRoot_c, ← c_xRoot_c, hconj]
  rw [xRoot_short_one_three_commutator_eq_short_two]
  rw [c_xRoot_c]
  rfl

theorem xRoot_short_three_five_commutator_eq_short_four :
    automorphismCommutator
        (xRoot (RootLength.Short, 3) true)
        (xRoot (RootLength.Short, 5) true) =
      xRoot (RootLength.Short, 4) true := by
  have hc : cAction (RootLength.Short, 2) = (RootLength.Short, 3) := by
    rfl
  have hc' : cAction (RootLength.Short, 4) = (RootLength.Short, 5) := by
    rfl
  have hconj (a b : SplitOctF2Aut) :
      automorphismCommutator (c * a * c⁻¹) (c * b * c⁻¹) =
        c * automorphismCommutator a b * c⁻¹ := by
    simp [automorphismCommutator, mul_assoc]
  rw [← hc, ← hc', ← c_xRoot_c, ← c_xRoot_c, hconj]
  rw [xRoot_short_two_four_commutator_eq_short_three]
  rw [c_xRoot_c]
  rfl

theorem xRoot_short_four_zero_commutator_eq_short_five :
    automorphismCommutator
        (xRoot (RootLength.Short, 4) true)
        (xRoot (RootLength.Short, 0) true) =
      xRoot (RootLength.Short, 5) true := by
  have hc : cAction (RootLength.Short, 3) = (RootLength.Short, 4) := by
    rfl
  have hc' : cAction (RootLength.Short, 5) = (RootLength.Short, 0) := by
    rfl
  have hconj (a b : SplitOctF2Aut) :
      automorphismCommutator (c * a * c⁻¹) (c * b * c⁻¹) =
        c * automorphismCommutator a b * c⁻¹ := by
    simp [automorphismCommutator, mul_assoc]
  rw [← hc, ← hc', ← c_xRoot_c, ← c_xRoot_c, hconj]
  rw [xRoot_short_three_five_commutator_eq_short_four]
  rw [c_xRoot_c]
  rfl

theorem xRoot_short_five_one_commutator_eq_short_zero :
    automorphismCommutator
        (xRoot (RootLength.Short, 5) true)
        (xRoot (RootLength.Short, 1) true) =
      xRoot (RootLength.Short, 0) true := by
  have hc : cAction (RootLength.Short, 4) = (RootLength.Short, 5) := by
    rfl
  have hc' : cAction (RootLength.Short, 0) = (RootLength.Short, 1) := by
    rfl
  have hconj (a b : SplitOctF2Aut) :
      automorphismCommutator (c * a * c⁻¹) (c * b * c⁻¹) =
        c * automorphismCommutator a b * c⁻¹ := by
    simp [automorphismCommutator, mul_assoc]
  rw [← hc, ← hc', ← c_xRoot_c, ← c_xRoot_c, hconj]
  rw [xRoot_short_four_zero_commutator_eq_short_five]
  rw [c_xRoot_c]
  rfl

theorem xRoot_short_zero_four_commutator_eq_short_five :
    automorphismCommutator
        (xRoot (RootLength.Short, 0) true)
        (xRoot (RootLength.Short, 4) true) =
      xRoot (RootLength.Short, 5) true := by
  apply autMatrix_injective
  decide

theorem xRoot_long_zero_one_commutator_eq_short_five :
    automorphismCommutator
        (xRoot (RootLength.Long, 0) true)
        (xRoot (RootLength.Long, 1) true) =
      xRoot (RootLength.Short, 5) true := by
  apply autMatrix_injective
  decide

theorem xRoot_long_one_two_commutator_eq_short_zero :
    automorphismCommutator
        (xRoot (RootLength.Long, 1) true)
        (xRoot (RootLength.Long, 2) true) =
      xRoot (RootLength.Short, 0) true := by
  apply autMatrix_injective
  decide

theorem xRoot_long_two_three_commutator_eq_short_one :
    automorphismCommutator
        (xRoot (RootLength.Long, 2) true)
        (xRoot (RootLength.Long, 3) true) =
      xRoot (RootLength.Short, 1) true := by
  apply autMatrix_injective
  decide

theorem xRoot_long_three_four_commutator_eq_short_two :
    automorphismCommutator
        (xRoot (RootLength.Long, 3) true)
        (xRoot (RootLength.Long, 4) true) =
      xRoot (RootLength.Short, 2) true := by
  apply autMatrix_injective
  decide

theorem xRoot_long_four_five_commutator_eq_short_three :
    automorphismCommutator
        (xRoot (RootLength.Long, 4) true)
        (xRoot (RootLength.Long, 5) true) =
      xRoot (RootLength.Short, 3) true := by
  apply autMatrix_injective
  decide

theorem xRoot_long_five_zero_commutator_eq_short_four :
    automorphismCommutator
        (xRoot (RootLength.Long, 5) true)
        (xRoot (RootLength.Long, 0) true) =
      xRoot (RootLength.Short, 4) true := by
  apply autMatrix_injective
  decide

theorem rootSubgroup_le_closure_of_root_commutator
    {α β γ : G2Root}
    (hcomm : automorphismCommutator
        (xRoot α true) (xRoot β true) = xRoot γ true) :
    rootSubgroup γ ≤
      Subgroup.closure
        ((rootSubgroup α : Set SplitOctF2Aut) ∪
          (rootSubgroup β : Set SplitOctF2Aut)) := by
  intro x hx
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective γ ⟨x, hx⟩
  cases t with
  | false =>
      have hx0 : xRoot γ false = x := congrArg Subtype.val ht
      rw [← hx0, native_root_zero]
      exact Subgroup.one_mem _
  | true =>
      let H : Subgroup SplitOctF2Aut := Subgroup.closure
        ((rootSubgroup α : Set SplitOctF2Aut) ∪
          (rootSubgroup β : Set SplitOctF2Aut))
      have hα : xRoot α true ∈ H :=
        Subgroup.subset_closure (Or.inl (native_root_mem α true))
      have hβ : xRoot β true ∈ H :=
        Subgroup.subset_closure (Or.inr (native_root_mem β true))
      have hc : automorphismCommutator
          (xRoot α true) (xRoot β true) ∈ H := by
        have hword := H.mul_mem (H.mul_mem (H.mul_mem hα hβ) (H.inv_mem hα))
          (H.inv_mem hβ)
        simpa [automorphismCommutator, H, mul_assoc] using hword
      have hx1 : xRoot γ true = x := congrArg Subtype.val ht
      rw [← hx1, ← hcomm]
      exact hc

theorem rootSubgroup_c_conjugate_mem
    (α : G2Root) {x : SplitOctF2Aut}
    (hx : x ∈ rootSubgroup α) :
    c * x * c⁻¹ ∈ rootSubgroup (cAction α) := by
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective α ⟨x, hx⟩
  have hxroot : x = xRoot α t := congrArg Subtype.val ht.symm
  rw [hxroot, c_xRoot_c]
  exact native_root_mem (cAction α) t

theorem rootSubgroup_s_conjugate_mem
    (α : G2Root) {x : SplitOctF2Aut}
    (hx : x ∈ rootSubgroup α) :
    s * x * s⁻¹ ∈ rootSubgroup (sAction α) := by
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective α ⟨x, hx⟩
  have hxroot : x = xRoot α t := congrArg Subtype.val ht.symm
  have hs : s⁻¹ = s := by
    apply mul_left_cancel (a := s)
    simp [s_sq]
  rw [hxroot, hs, s_xRoot_s]
  exact native_root_mem (sAction α) t

theorem rootSubgroup_short_three_le_long_four_long_five_closure :
    rootSubgroup (RootLength.Short, 3) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Long, 4) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Long, 5) : Set SplitOctF2Aut)) := by
  exact rootSubgroup_le_closure_of_root_commutator
    xRoot_long_four_five_commutator_eq_short_three

theorem rootSubgroup_short_four_le_long_five_long_zero_closure :
    rootSubgroup (RootLength.Short, 4) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Long, 5) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Long, 0) : Set SplitOctF2Aut)) := by
  exact rootSubgroup_le_closure_of_root_commutator
    xRoot_long_five_zero_commutator_eq_short_four

theorem rootSubgroup_short_one_le_long_two_long_three_closure :
    rootSubgroup (RootLength.Short, 1) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Long, 2) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Long, 3) : Set SplitOctF2Aut)) := by
  exact rootSubgroup_le_closure_of_root_commutator
    xRoot_long_two_three_commutator_eq_short_one

theorem rootSubgroup_short_two_le_long_three_long_four_closure :
    rootSubgroup (RootLength.Short, 2) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Long, 3) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Long, 4) : Set SplitOctF2Aut)) := by
  exact rootSubgroup_le_closure_of_root_commutator
    xRoot_long_three_four_commutator_eq_short_two

theorem rootSubgroup_short_five_le_long_zero_long_one_closure :
    rootSubgroup (RootLength.Short, 5) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Long, 0) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Long, 1) : Set SplitOctF2Aut)) := by
  exact rootSubgroup_le_closure_of_root_commutator
    xRoot_long_zero_one_commutator_eq_short_five

theorem rootSubgroup_short_zero_le_short_five_short_one_closure :
    rootSubgroup (RootLength.Short, 0) ≤
      Subgroup.closure
        ((rootSubgroup (RootLength.Short, 5) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut)) := by
  intro x hx
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective (RootLength.Short, 0) ⟨x, hx⟩
  cases t with
  | false =>
      have hx0 : xRoot (RootLength.Short, 0) false = x :=
        congrArg Subtype.val ht
      rw [← hx0, native_root_zero]
      exact Subgroup.one_mem _
  | true =>
      let H : Subgroup SplitOctF2Aut := Subgroup.closure
        ((rootSubgroup (RootLength.Short, 5) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut))
      have h5 : xRoot (RootLength.Short, 5) true ∈ H :=
        Subgroup.subset_closure (Or.inl
          (native_root_mem (RootLength.Short, 5) true))
      have h1 : xRoot (RootLength.Short, 1) true ∈ H :=
        Subgroup.subset_closure (Or.inr
          (native_root_mem (RootLength.Short, 1) true))
      have hc := H.mul_mem (H.mul_mem h5 h1) (H.inv_mem h5)
      have hc := H.mul_mem hc (H.inv_mem h1)
      have hx0 : xRoot (RootLength.Short, 0) true = x :=
        congrArg Subtype.val ht
      rw [← hx0]
      have hcomm : automorphismCommutator
          (xRoot (RootLength.Short, 5) true)
          (xRoot (RootLength.Short, 1) true) ∈ H := by
        simpa [automorphismCommutator, H, mul_assoc] using hc
      rw [xRoot_short_five_one_commutator_eq_short_zero] at hcomm
      exact hcomm

theorem rootSubgroup_short_zero_le_positiveRootSubgroup :
    rootSubgroup (RootLength.Short, 0) ≤ positiveRootSubgroup := by
  intro x hx
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective (RootLength.Short, 0) ⟨x, hx⟩
  cases t with
  | false =>
      have hx0 : xRoot (RootLength.Short, 0) false = x :=
        congrArg Subtype.val ht
      rw [← hx0, native_root_zero]
      exact positiveRootSubgroup.one_mem
  | true =>
      have hx1 : xRoot (RootLength.Short, 0) true = x :=
        congrArg Subtype.val ht
      rw [← hx1, xRoot_short_zero_true_eq_positiveRootPacket_zero]
      exact positiveRootPacket_mem_subgroup 0

/-! The two-root product image is kept separate from any claim that it is a
    whole residual subgroup.  This owner proves only the membership edge that
    is available from the native root-subgroup data. -/

def rootProductSubgroup (α β : G2Root) : Subgroup SplitOctF2Aut :=
  Subgroup.closure (rootSubgroup α ∪ rootSubgroup β : Set SplitOctF2Aut)

theorem sAction_involutive (α : G2Root) :
    sAction (sAction α) = α := by
  rcases α with ⟨l, k⟩
  cases l <;> fin_cases k <;> rfl

theorem cAction_surjective : Function.Surjective cAction := by
  intro ⟨l, k⟩
  refine ⟨(l, k - 1), ?_⟩
  cases l <;> fin_cases k <;> rfl

theorem rootSubgroup_le_rootProductSubgroup_left (α β : G2Root) :
    rootSubgroup α ≤ rootProductSubgroup α β := by
  intro x hx
  apply Subgroup.subset_closure
  exact Set.mem_union_left _ hx

theorem rootSubgroup_le_rootProductSubgroup_right (α β : G2Root) :
    rootSubgroup β ≤ rootProductSubgroup α β := by
  intro x hx
  apply Subgroup.subset_closure
  exact Set.mem_union_right _ hx

theorem rootSubgroup_short_one_le_short_zero_short_two_productSubgroup :
    rootSubgroup (RootLength.Short, 1) ≤
      rootProductSubgroup (RootLength.Short, 0) (RootLength.Short, 2) := by
  intro x hx
  obtain ⟨t, ht⟩ := rootSubgroupMap_surjective (RootLength.Short, 1) ⟨x, hx⟩
  cases t with
  | false =>
      have hx0 : xRoot (RootLength.Short, 1) false = x :=
        congrArg Subtype.val ht
      rw [← hx0, native_root_zero]
      exact (rootProductSubgroup (RootLength.Short, 0)
        (RootLength.Short, 2)).one_mem
  | true =>
      have h0 : xRoot (RootLength.Short, 0) true ∈
          rootProductSubgroup (RootLength.Short, 0) (RootLength.Short, 2) :=
        rootSubgroup_le_rootProductSubgroup_left _ _
          (native_root_mem (RootLength.Short, 0) true)
      have h2 : xRoot (RootLength.Short, 2) true ∈
          rootProductSubgroup (RootLength.Short, 0) (RootLength.Short, 2) :=
        rootSubgroup_le_rootProductSubgroup_right _ _
          (native_root_mem (RootLength.Short, 2) true)
      have hc := (rootProductSubgroup (RootLength.Short, 0)
        (RootLength.Short, 2)).mul_mem
          ((rootProductSubgroup (RootLength.Short, 0)
            (RootLength.Short, 2)).mul_mem h0 h2)
          ((rootProductSubgroup (RootLength.Short, 0)
            (RootLength.Short, 2)).inv_mem h0)
      have hc := (rootProductSubgroup (RootLength.Short, 0)
        (RootLength.Short, 2)).mul_mem hc
        ((rootProductSubgroup (RootLength.Short, 0)
          (RootLength.Short, 2)).inv_mem h2)
      have hx1 : xRoot (RootLength.Short, 1) true = x :=
        congrArg Subtype.val ht
      rw [← hx1, xRoot]
      have hcomm : automorphismCommutator
          (xRoot (RootLength.Short, 0) true)
          (xRoot (RootLength.Short, 2) true) ∈
          rootProductSubgroup (RootLength.Short, 0) (RootLength.Short, 2) := by
        simpa [automorphismCommutator, mul_assoc] using hc
      rw [native_root_commutator_short_0_2] at hcomm
      exact hcomm

theorem rootProductSubgroup_short_zero_short_two_eq_three_root_closure :
    rootProductSubgroup (RootLength.Short, 0) (RootLength.Short, 2) =
      Subgroup.closure
        ((rootSubgroup (RootLength.Short, 0) : Set SplitOctF2Aut) ∪
          ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
            (rootSubgroup (RootLength.Short, 2) : Set SplitOctF2Aut))) := by
  apply le_antisymm
  · rw [rootProductSubgroup, Subgroup.closure_le]
    rintro x (hx | hx)
    · apply Subgroup.subset_closure
      change x ∈ (rootSubgroup (RootLength.Short, 0) : Set SplitOctF2Aut) ∪
        ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Short, 2) : Set SplitOctF2Aut))
      exact Or.inl hx
    · apply Subgroup.subset_closure
      change x ∈ (rootSubgroup (RootLength.Short, 0) : Set SplitOctF2Aut) ∪
        ((rootSubgroup (RootLength.Short, 1) : Set SplitOctF2Aut) ∪
          (rootSubgroup (RootLength.Short, 2) : Set SplitOctF2Aut))
      exact Or.inr (Or.inr hx)
  · rw [Subgroup.closure_le]
    rintro x hx
    rcases hx with hx | hx
    · exact rootSubgroup_le_rootProductSubgroup_left _ _ hx
    · rcases hx with hx | hx
      · exact rootSubgroup_short_one_le_short_zero_short_two_productSubgroup hx
      · exact rootSubgroup_le_rootProductSubgroup_right _ _ hx

theorem rootProductSubgroup_same_eq_rootSubgroup (α : G2Root) :
    rootProductSubgroup α α = rootSubgroup α := by
  apply le_antisymm
  · change Subgroup.closure (rootSubgroup α ∪ rootSubgroup α : Set SplitOctF2Aut) ≤
      rootSubgroup α
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact hx
  · intro x hx
    apply Subgroup.subset_closure
    exact Set.mem_union_left _ hx

def rootProductImage (α β : G2Root) : Set SplitOctF2Aut :=
  Set.range (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)

theorem rootAut_short_zero_ne_short_two :
    rootAut (RootLength.Short, 0) ≠ rootAut (RootLength.Short, 2) := by
  intro h
  have hc := rootAut_commutator_S0_S2
  rw [h] at hc
  have hs2 : (rootAut (RootLength.Short, 2))⁻¹ =
      rootAut (RootLength.Short, 2) := by
    apply inv_eq_of_mul_eq_one_left
    exact rootAut_sq (RootLength.Short, 2)
  have hc' :
      (1 : SplitOctF2Aut) = rootAut (RootLength.Short, 1) := by
    simpa [automorphismCommutator, rootAut_sq, hs2] using hc
  exact rootAut_ne_one (RootLength.Short, 1) hc'.symm

theorem short_zero_short_two_product_injective :
    Function.Injective
      (fun e : Bool × Bool =>
        xRoot (RootLength.Short, 0) e.1 *
          xRoot (RootLength.Short, 2) e.2) := by
  have hA : rootAut (RootLength.Short, 0) ≠
      (1 : SplitOctF2Aut) := rootAut_ne_one (RootLength.Short, 0)
  have hB : rootAut (RootLength.Short, 2) ≠
      (1 : SplitOctF2Aut) := rootAut_ne_one (RootLength.Short, 2)
  have hAB : rootAut (RootLength.Short, 0) *
      rootAut (RootLength.Short, 2) ≠ (1 : SplitOctF2Aut) := by
    intro hab
    apply rootAut_short_zero_ne_short_two
    calc
      rootAut (RootLength.Short, 0) =
          rootAut (RootLength.Short, 0) * 1 := by simp
      _ = rootAut (RootLength.Short, 0) *
          (rootAut (RootLength.Short, 2) *
            rootAut (RootLength.Short, 2)) := by
            rw [rootAut_sq]
      _ = (rootAut (RootLength.Short, 0) *
          rootAut (RootLength.Short, 2)) *
          rootAut (RootLength.Short, 2) := by simp [mul_assoc]
      _ = rootAut (RootLength.Short, 2) := by rw [hab]; simp
  intro e e' h
  rcases e with ⟨e₁, e₂⟩
  rcases e' with ⟨e₁', e₂'⟩
  cases e₁ <;> cases e₂ <;> cases e₁' <;> cases e₂' <;>
    simp [xRoot] at h ⊢
  all_goals
    first
    | exact hA h
    | exact hB h
    | exact hAB h
    | exact hA h.symm
    | exact hB h.symm
    | exact hAB h.symm
    | exact rootAut_short_zero_ne_short_two h
    | exact rootAut_short_zero_ne_short_two h.symm

theorem cAction_product_injective_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    Function.Injective
      (fun e : Bool × Bool =>
        xRoot (cAction α) e.1 * xRoot (cAction β) e.2) := by
  intro e e' h
  apply hinj
  have h' := congrArg (fun z : SplitOctF2Aut => c⁻¹ * z * c) h
  dsimp at h'
  rw [← c_xRoot_c α e.1, ← c_xRoot_c β e.2,
    ← c_xRoot_c α e'.1, ← c_xRoot_c β e'.2] at h'
  simpa [mul_assoc] using h'

theorem cAction_short_zero_short_two_product_injective :
    Function.Injective
      (fun e : Bool × Bool =>
        xRoot (cAction (RootLength.Short, 0)) e.1 *
          xRoot (cAction (RootLength.Short, 2)) e.2) := by
  exact cAction_product_injective_of_injective
    (RootLength.Short, 0) (RootLength.Short, 2)
    short_zero_short_two_product_injective

theorem sAction_product_injective_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    Function.Injective
      (fun e : Bool × Bool =>
        xRoot (sAction α) e.1 * xRoot (sAction β) e.2) := by
  intro e e' h
  apply hinj
  have hs : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_left
    exact s_sq
  have h' := congrArg (fun z : SplitOctF2Aut => s⁻¹ * z * s) h
  dsimp at h'
  rw [hs, ← s_xRoot_s α e.1, ← s_xRoot_s β e.2,
    ← s_xRoot_s α e'.1, ← s_xRoot_s β e'.2] at h'
  simpa [mul_assoc] using h'

theorem sAction_short_zero_short_two_product_injective :
    Function.Injective
      (fun e : Bool × Bool =>
        xRoot (sAction (RootLength.Short, 0)) e.1 *
          xRoot (sAction (RootLength.Short, 2)) e.2) := by
  exact sAction_product_injective_of_injective
    (RootLength.Short, 0) (RootLength.Short, 2)
    short_zero_short_two_product_injective

theorem cAction_product_eq_conjugate (α β : G2Root) (e : Bool × Bool) :
    xRoot (cAction α) e.1 * xRoot (cAction β) e.2 =
      c * (xRoot α e.1 * xRoot β e.2) * c⁻¹ := by
  calc
    xRoot (cAction α) e.1 * xRoot (cAction β) e.2 =
        (c * xRoot α e.1 * c⁻¹) *
          (c * xRoot β e.2 * c⁻¹) := by
      rw [c_xRoot_c α e.1, c_xRoot_c β e.2]
    _ = c * (xRoot α e.1 * xRoot β e.2) * c⁻¹ := by
      simp [mul_assoc]

theorem sAction_product_eq_conjugate (α β : G2Root) (e : Bool × Bool) :
    xRoot (sAction α) e.1 * xRoot (sAction β) e.2 =
      s * (xRoot α e.1 * xRoot β e.2) * s⁻¹ := by
  have hs : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_left
    exact s_sq
  calc
    xRoot (sAction α) e.1 * xRoot (sAction β) e.2 =
        (s * xRoot α e.1 * s) *
          (s * xRoot β e.2 * s) := by
      rw [s_xRoot_s α e.1, s_xRoot_s β e.2]
    _ = s * (xRoot α e.1 * xRoot β e.2) * s⁻¹ := by
      calc
        (s * xRoot α e.1 * s) *
            (s * xRoot β e.2 * s) =
            s * xRoot α e.1 * (s * s) *
              xRoot β e.2 * s := by simp [mul_assoc]
        _ = s * (xRoot α e.1 * xRoot β e.2) * s := by
          rw [s_sq]
          group
        _ = s * (xRoot α e.1 * xRoot β e.2) * s⁻¹ := by rw [hs]

def conjugateSet (g : SplitOctF2Aut) (S : Set SplitOctF2Aut) :
    Set SplitOctF2Aut :=
  (fun x => g * x * g⁻¹) '' S

def conjugationHom (g : SplitOctF2Aut) :
    SplitOctF2Aut →* SplitOctF2Aut where
  toFun x := g * x * g⁻¹
  map_one' := by simp
  map_mul' x y := by simp [mul_assoc]

theorem conjugationHom_injective (g : SplitOctF2Aut) :
    Function.Injective (conjugationHom g) := by
  intro x y h
  apply mul_left_cancel (a := g⁻¹)
  apply mul_right_cancel (b := g)
  simpa [conjugationHom, mul_assoc] using h

theorem conjugationHom_inv_apply (g x : SplitOctF2Aut) :
    conjugationHom g⁻¹ (conjugationHom g x) = x := by
  simp [conjugationHom, mul_assoc]

theorem conjugationHom_apply_inv (g x : SplitOctF2Aut) :
    conjugationHom g (conjugationHom g⁻¹ x) = x := by
  simp [conjugationHom, mul_assoc]

theorem cAction_rootProductImage_eq_conjugateSet
    (α β : G2Root) :
    rootProductImage (cAction α) (cAction β) =
      conjugateSet c (rootProductImage α β) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨xRoot α e.1 * xRoot β e.2, ⟨e, rfl⟩, ?_⟩
    exact (cAction_product_eq_conjugate α β e).symm
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, cAction_product_eq_conjugate α β e⟩

theorem sAction_rootProductImage_eq_conjugateSet
    (α β : G2Root) :
    rootProductImage (sAction α) (sAction β) =
      conjugateSet s (rootProductImage α β) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨xRoot α e.1 * xRoot β e.2, ⟨e, rfl⟩, ?_⟩
    exact (sAction_product_eq_conjugate α β e).symm
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, sAction_product_eq_conjugate α β e⟩

noncomputable def rootProductImage_equiv_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    (Bool × Bool) ≃ {x : SplitOctF2Aut // x ∈ rootProductImage α β} :=
  Equiv.ofInjective
    (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2) hinj

theorem rootProductImage_card_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    Nat.card {x : SplitOctF2Aut // x ∈ rootProductImage α β} = 4 := by
  simpa using (Nat.card_congr (rootProductImage_equiv_of_injective α β hinj)).symm

theorem cAction_rootProductImage_card_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    Nat.card {x : SplitOctF2Aut //
      x ∈ rootProductImage (cAction α) (cAction β)} = 4 := by
  exact rootProductImage_card_of_injective
    (cAction α) (cAction β)
    (cAction_product_injective_of_injective α β hinj)

theorem sAction_rootProductImage_card_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    Nat.card {x : SplitOctF2Aut //
      x ∈ rootProductImage (sAction α) (sAction β)} = 4 := by
  exact rootProductImage_card_of_injective
    (sAction α) (sAction β)
    (sAction_product_injective_of_injective α β hinj)

theorem cAction_short_zero_short_two_product_image_card :
    Nat.card {x : SplitOctF2Aut //
      x ∈ rootProductImage
        (cAction (RootLength.Short, 0))
        (cAction (RootLength.Short, 2))} = 4 := by
  exact rootProductImage_card_of_injective
    (cAction (RootLength.Short, 0))
    (cAction (RootLength.Short, 2))
    cAction_short_zero_short_two_product_injective

theorem sAction_short_zero_short_two_product_image_card :
    Nat.card {x : SplitOctF2Aut //
      x ∈ rootProductImage
        (sAction (RootLength.Short, 0))
        (sAction (RootLength.Short, 2))} = 4 := by
  exact rootProductImage_card_of_injective
    (sAction (RootLength.Short, 0))
    (sAction (RootLength.Short, 2))
    sAction_short_zero_short_two_product_injective

theorem rootProductImage_subset_rootProductSubgroup (α β : G2Root) :
    rootProductImage α β ⊆ (rootProductSubgroup α β : Set SplitOctF2Aut) := by
  rintro _ ⟨e, rfl⟩
  apply (rootProductSubgroup α β).mul_mem
  · apply Subgroup.subset_closure
    exact Set.mem_union_left _ (native_root_mem α e.1)
  · apply Subgroup.subset_closure
    exact Set.mem_union_right _ (native_root_mem β e.2)

theorem conjugateSet_rootProductImage_subset_cAction_rootProductSubgroup
    (α β : G2Root) :
    conjugateSet c (rootProductImage α β) ⊆
      (rootProductSubgroup (cAction α) (cAction β) : Set SplitOctF2Aut) := by
  rw [← cAction_rootProductImage_eq_conjugateSet α β]
  exact rootProductImage_subset_rootProductSubgroup
    (cAction α) (cAction β)

theorem conjugateSet_rootProductImage_subset_sAction_rootProductSubgroup
    (α β : G2Root) :
    conjugateSet s (rootProductImage α β) ⊆
      (rootProductSubgroup (sAction α) (sAction β) : Set SplitOctF2Aut) := by
  rw [← sAction_rootProductImage_eq_conjugateSet α β]
  exact rootProductImage_subset_rootProductSubgroup
    (sAction α) (sAction β)

theorem rootProductImage_mem_rootProductSubgroup
    (α β : G2Root) (e : Bool × Bool) :
    xRoot α e.1 * xRoot β e.2 ∈ rootProductSubgroup α β := by
  exact rootProductImage_subset_rootProductSubgroup α β ⟨e, rfl⟩

theorem rootProductSubgroup_card_ge_four_of_injective
    (α β : G2Root)
    (hinj : Function.Injective
      (fun e : Bool × Bool => xRoot α e.1 * xRoot β e.2)) :
    4 ≤ Nat.card (rootProductSubgroup α β) := by
  let f : (Bool × Bool) → rootProductSubgroup α β := fun e =>
    ⟨xRoot α e.1 * xRoot β e.2,
      rootProductImage_mem_rootProductSubgroup α β e⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply hinj
    exact congrArg Subtype.val h
  have hcard := Nat.card_le_card_of_injective f hf
  simpa using hcard

theorem short_zero_short_two_product_image_card :
    Nat.card {x : SplitOctF2Aut //
      x ∈ rootProductImage (RootLength.Short, 0) (RootLength.Short, 2)} = 4 := by
  exact rootProductImage_card_of_injective
    (RootLength.Short, 0) (RootLength.Short, 2)
    short_zero_short_two_product_injective

theorem short_zero_short_two_product_subgroup_card_ge_four :
    4 ≤ Nat.card
      (rootProductSubgroup (RootLength.Short, 0) (RootLength.Short, 2)) := by
  exact rootProductSubgroup_card_ge_four_of_injective
    (RootLength.Short, 0) (RootLength.Short, 2)
    short_zero_short_two_product_injective

theorem rootProductImage_same_eq_root_range (α : G2Root) :
    rootProductImage α α = Set.range (xRoot α) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨e.1 ^^ e.2, ?_⟩
    change xRoot α (e.1 ^^ e.2) = xRoot α e.1 * xRoot α e.2
    exact native_root_additive α e.1 e.2
  · rintro ⟨t, rfl⟩
    refine ⟨(t, false), ?_⟩
    change xRoot α t * xRoot α false = xRoot α t
    rw [native_root_zero]
    simp

theorem root_range_eq_rootSubgroup_carrier (α : G2Root) :
    Set.range (xRoot α) = (rootSubgroup α : Set SplitOctF2Aut) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (rootSubgroupMap α t).property
  · intro hx
    obtain ⟨t, ht⟩ := rootSubgroupMap_surjective α ⟨x, hx⟩
    exact ⟨t, congrArg Subtype.val ht⟩

theorem conjugationHom_map_rootProductSubgroup_le_cAction
    (α β : G2Root) :
    Subgroup.map (conjugationHom c) (rootProductSubgroup α β) ≤
      rootProductSubgroup (cAction α) (cAction β) := by
  rw [rootProductSubgroup, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · obtain ⟨t, ht⟩ := rootSubgroupMap_surjective α ⟨x, hx⟩
    apply Subgroup.subset_closure
    apply Set.mem_union_left
    change c * x * c⁻¹ ∈ rootSubgroup (cAction α)
    have hxroot : x = xRoot α t := congrArg Subtype.val ht.symm
    rw [hxroot, c_xRoot_c]
    exact native_root_mem (cAction α) t
  · obtain ⟨t, ht⟩ := rootSubgroupMap_surjective β ⟨x, hx⟩
    apply Subgroup.subset_closure
    apply Set.mem_union_right
    change c * x * c⁻¹ ∈ rootSubgroup (cAction β)
    have hxroot : x = xRoot β t := congrArg Subtype.val ht.symm
    rw [hxroot, c_xRoot_c]
    exact native_root_mem (cAction β) t

theorem conjugationHom_inv_map_cAction_rootProductSubgroup_le
    (α β : G2Root) :
    Subgroup.map (conjugationHom c⁻¹)
        (rootProductSubgroup (cAction α) (cAction β)) ≤
      rootProductSubgroup α β := by
  rw [rootProductSubgroup, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · obtain ⟨t, ht⟩ := rootSubgroupMap_surjective (cAction α) ⟨x, hx⟩
    apply Subgroup.subset_closure
    apply Set.mem_union_left
    change c⁻¹ * x * c ∈ rootSubgroup α
    have hxroot : x = xRoot (cAction α) t := congrArg Subtype.val ht.symm
    rw [hxroot, ← c_xRoot_c α t]
    group
    exact native_root_mem α t
  · obtain ⟨t, ht⟩ := rootSubgroupMap_surjective (cAction β) ⟨x, hx⟩
    apply Subgroup.subset_closure
    apply Set.mem_union_right
    change c⁻¹ * x * c ∈ rootSubgroup β
    have hxroot : x = xRoot (cAction β) t := congrArg Subtype.val ht.symm
    rw [hxroot, ← c_xRoot_c β t]
    group
    exact native_root_mem β t

theorem conjugationHom_map_rootProductSubgroup_eq_cAction
    (α β : G2Root) :
    Subgroup.map (conjugationHom c) (rootProductSubgroup α β) =
      rootProductSubgroup (cAction α) (cAction β) := by
  apply le_antisymm
  · exact conjugationHom_map_rootProductSubgroup_le_cAction α β
  · intro x hx
    have hx' : conjugationHom c⁻¹ x ∈ rootProductSubgroup α β :=
      conjugationHom_inv_map_cAction_rootProductSubgroup_le α β ⟨x, hx, rfl⟩
    refine ⟨conjugationHom c⁻¹ x, hx', ?_⟩
    exact (conjugationHom_inv_apply c x).symm

theorem conjugationHom_map_rootProductSubgroup_le_sAction
    (α β : G2Root) :
    Subgroup.map (conjugationHom s) (rootProductSubgroup α β) ≤
      rootProductSubgroup (sAction α) (sAction β) := by
  have hs : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_left
    exact s_sq
  rw [rootProductSubgroup, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · obtain ⟨t, ht⟩ := rootSubgroupMap_surjective α ⟨x, hx⟩
    apply Subgroup.subset_closure
    apply Set.mem_union_left
    change s * x * s⁻¹ ∈ rootSubgroup (sAction α)
    have hxroot : x = xRoot α t := congrArg Subtype.val ht.symm
    rw [hxroot, hs, s_xRoot_s]
    exact native_root_mem (sAction α) t
  · obtain ⟨t, ht⟩ := rootSubgroupMap_surjective β ⟨x, hx⟩
    apply Subgroup.subset_closure
    apply Set.mem_union_right
    change s * x * s⁻¹ ∈ rootSubgroup (sAction β)
    have hxroot : x = xRoot β t := congrArg Subtype.val ht.symm
    rw [hxroot, hs, s_xRoot_s]
    exact native_root_mem (sAction β) t

theorem conjugationHom_map_sAction_rootProductSubgroup_le
    (α β : G2Root) :
    Subgroup.map (conjugationHom s)
        (rootProductSubgroup (sAction α) (sAction β)) ≤
      rootProductSubgroup α β := by
  simpa only [sAction_involutive] using
    (conjugationHom_map_rootProductSubgroup_le_sAction
      (sAction α) (sAction β))

theorem conjugationHom_map_rootProductSubgroup_eq_sAction
    (α β : G2Root) :
    Subgroup.map (conjugationHom s) (rootProductSubgroup α β) =
      rootProductSubgroup (sAction α) (sAction β) := by
  apply le_antisymm
  · exact conjugationHom_map_rootProductSubgroup_le_sAction α β
  · intro x hx
    have hx' : conjugationHom s x ∈ rootProductSubgroup α β := by
      exact conjugationHom_map_sAction_rootProductSubgroup_le α β ⟨x, hx, rfl⟩
    refine ⟨conjugationHom s x, hx', ?_⟩
    exact (conjugationHom_apply_inv s x).symm

theorem rootSubgroup_carrier_subset_rootProductImage_left (α β : G2Root) :
    (rootSubgroup α : Set SplitOctF2Aut) ⊆ rootProductImage α β := by
  rw [← root_range_eq_rootSubgroup_carrier]
  rintro _ ⟨t, rfl⟩
  refine ⟨(t, false), ?_⟩
  change xRoot α t * xRoot β false = xRoot α t
  rw [native_root_zero]
  simp

theorem rootSubgroup_carrier_subset_rootProductImage_right (α β : G2Root) :
    (rootSubgroup β : Set SplitOctF2Aut) ⊆ rootProductImage α β := by
  rw [← root_range_eq_rootSubgroup_carrier]
  rintro _ ⟨t, rfl⟩
  refine ⟨(false, t), ?_⟩
  change xRoot α false * xRoot β t = xRoot β t
  rw [native_root_zero]
  simp

theorem rootProductImage_same_eq_rootSubgroup_carrier (α : G2Root) :
    rootProductImage α α = (rootSubgroup α : Set SplitOctF2Aut) := by
  rw [rootProductImage_same_eq_root_range,
    root_range_eq_rootSubgroup_carrier]

theorem rootProductImage_same_eq_rootProductSubgroup_carrier (α : G2Root) :
    rootProductImage α α = (rootProductSubgroup α α : Set SplitOctF2Aut) := by
  rw [rootProductImage_same_eq_rootSubgroup_carrier,
    rootProductSubgroup_same_eq_rootSubgroup]

theorem rootProductSubgroup_same_card (α : G2Root) :
    Nat.card (rootProductSubgroup α α) = 2 := by
  rw [rootProductSubgroup_same_eq_rootSubgroup]
  exact rootSubgroup_card α

theorem rootProductImage_same_card (α : G2Root) :
    Nat.card {x : SplitOctF2Aut // x ∈ rootProductImage α α} = 2 := by
  rw [rootProductImage_same_eq_root_range]
  rw [Nat.card_range_of_injective (native_root_injective α)]
  simp

end InfoGeometry.Algebra.Zorn.G2NativeRootProductImage
