import InfoGeometry.Algebra.Zorn.G2UnipotentWord6Cardinality

namespace InfoGeometry.Algebra.Zorn.G2NativeOrderedRootProduct

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Unipotent
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2UnipotentWord6Cardinality

/-!
# Native ordered root-product coordinates

The six-factor product is a genuine native construction.  This owner records
the part which is already proved internally: its Boolean coordinates are
unique, and hence it is equivalent to its image.  The image is deliberately
not identified with `positiveRootSubgroup`; the existing native development
proves inclusion and a cardinality lower bound, but not equality.
-/

theorem unipotentWord6_injective :
    Function.Injective unipotentWord6 := by
  exact unipotentWord6_injective_of_coordinate_separators
    unipotentWord6_up1_x0_readback
    unipotentWord6_down1_y2_readback
    unipotentWord6_up2_x0_readback
    unipotentWord6_down2_y0_readback
    unipotentWord6_up0_x1_readback
    unipotentWord6_down2_y1_readback

noncomputable def nativeOrderedRootProductEquiv :
    (Fin 6 → Bool) ≃ Set.range unipotentWord6 :=
  Equiv.ofInjective unipotentWord6 unipotentWord6_injective

theorem nativeOrderedRootProduct_mem
    (b : Fin 6 → Bool) :
    unipotentWord6 b ∈ positiveRootSubgroup :=
  unipotentWord6_mem_positiveRootSubgroup b

theorem positiveRootAction_inv (i : Fin 6) (t : Bool) :
    (positiveRootAction i t)⁻¹ = positiveRootAction i t := by
  cases t
  · simp [positiveRootAction]
  · apply inv_eq_of_mul_eq_one_left
    simpa [positiveRootAction] using (positiveRootPacket_sq i)

theorem unipotentWord6_inv_eq_reverse (b : Fin 6 → Bool) :
    (unipotentWord6 b)⁻¹ =
      positiveRootAction 5 (b 5) *
      positiveRootAction 4 (b 4) *
      positiveRootAction 3 (b 3) *
      positiveRootAction 2 (b 2) *
      positiveRootAction 1 (b 1) *
      positiveRootAction 0 (b 0) := by
  simp only [unipotentWord6, mul_inv_rev, positiveRootAction_inv]
  simp only [← mul_assoc]

theorem unipotentWord6_inv_mem_positiveRootSubgroup (b : Fin 6 → Bool) :
    (unipotentWord6 b)⁻¹ ∈ positiveRootSubgroup := by
  exact positiveRootSubgroup_inv_mem (unipotentWord6_mem_positiveRootSubgroup b)

theorem positiveRootPacket_mem_orderedRootProduct_range (i : Fin 6) :
    positiveRootPacket i ∈ Set.range unipotentWord6 := by
  refine ⟨fun j => if j = i then true else false, ?_⟩
  fin_cases i <;>
    simp [unipotentWord6, positiveRootAction, positiveRootPacket]

theorem positiveRootPacket_inv_mem_orderedRootProduct_range (i : Fin 6) :
    (positiveRootPacket i)⁻¹ ∈ Set.range unipotentWord6 := by
  rw [inv_eq_of_mul_eq_one_left (positiveRootPacket_sq i)]
  exact positiveRootPacket_mem_orderedRootProduct_range i

theorem positiveRootAction_mem_orderedRootProduct_range (i : Fin 6) (t : Bool) :
    positiveRootAction i t ∈ Set.range unipotentWord6 := by
  cases t
  · refine ⟨fun _ => false, ?_⟩
    simp [unipotentWord6, positiveRootAction]
  · exact positiveRootPacket_mem_orderedRootProduct_range i

theorem positiveRootAction_mul_eq_action_xor (i : Fin 6) (s t : Bool) :
    positiveRootAction i s * positiveRootAction i t =
      positiveRootAction i (s ^^ t) := by
  exact (positiveRootAction_add i s t).symm

theorem positiveRootAction_mul_mem_orderedRootProduct_range
    (i : Fin 6) (s t : Bool) :
    positiveRootAction i s * positiveRootAction i t ∈ Set.range unipotentWord6 := by
  rw [positiveRootAction_mul_eq_action_xor]
  exact positiveRootAction_mem_orderedRootProduct_range i (s ^^ t)

theorem swap_of_involutions {a b c : SplitOctF2Aut}
    (ha : a * a = 1) (hb : b * b = 1)
    (hc : c = a * b * a * b) :
    a * b = c * b * a := by
  rw [hc]
  simp [mul_assoc, ha, hb]

theorem positiveRootPacket_swap_0_1 :
    positiveRootPacket 0 * positiveRootPacket 1 =
      positiveRootPacket 2 * positiveRootPacket 1 * positiveRootPacket 0 := by
  apply swap_of_involutions
    (positiveRootPacket_sq 0) (positiveRootPacket_sq 1)
  exact positiveRootPacket_commutator_0_1.symm

theorem positiveRootPacket_swap_0_3 :
    positiveRootPacket 0 * positiveRootPacket 3 =
      positiveRootPacket 5 * positiveRootPacket 3 * positiveRootPacket 0 := by
  apply swap_of_involutions
    (positiveRootPacket_sq 0) (positiveRootPacket_sq 3)
  exact positiveRootPacket_commutator_0_3.symm

theorem positiveRootPacket_swap_1_3 :
    positiveRootPacket 1 * positiveRootPacket 3 =
      positiveRootPacket 4 * positiveRootPacket 3 * positiveRootPacket 1 := by
  apply swap_of_involutions
    (positiveRootPacket_sq 1) (positiveRootPacket_sq 3)
  exact positiveRootPacket_commutator_1_3.symm

theorem positiveRootPacket_swap_2_4 :
    positiveRootPacket 2 * positiveRootPacket 4 =
      positiveRootPacket 1 * positiveRootPacket 4 * positiveRootPacket 2 := by
  apply swap_of_involutions
    (positiveRootPacket_sq 2) (positiveRootPacket_sq 4)
  exact positiveRootPacket_commutator_2_4.symm

theorem positiveRootPacket_swap_2_5 :
    positiveRootPacket 2 * positiveRootPacket 5 =
      positiveRootPacket 0 * positiveRootPacket 5 * positiveRootPacket 2 := by
  apply swap_of_involutions
    (positiveRootPacket_sq 2) (positiveRootPacket_sq 5)
  exact positiveRootPacket_commutator_2_5.symm

theorem positiveRootPacket_swap_4_5 :
    positiveRootPacket 4 * positiveRootPacket 5 =
      positiveRootPacket 3 * positiveRootPacket 5 * positiveRootPacket 4 := by
  apply swap_of_involutions
    (positiveRootPacket_sq 4) (positiveRootPacket_sq 5)
  exact positiveRootPacket_commutator_4_5.symm

theorem positiveRootAction_comm_0_2 (s t : Bool) :
    positiveRootAction 0 s * positiveRootAction 2 t =
      positiveRootAction 2 t * positiveRootAction 0 s := by
  cases s <;> cases t
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simpa [positiveRootAction] using positiveRootPacket_comm_0_2

theorem positiveRootAction_comm_0_5 (s t : Bool) :
    positiveRootAction 0 s * positiveRootAction 5 t =
      positiveRootAction 5 t * positiveRootAction 0 s := by
  cases s <;> cases t
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simpa [positiveRootAction] using positiveRootPacket_comm_0_5

theorem positiveRootAction_comm_1_4 (s t : Bool) :
    positiveRootAction 1 s * positiveRootAction 4 t =
      positiveRootAction 4 t * positiveRootAction 1 s := by
  cases s <;> cases t
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simpa [positiveRootAction] using positiveRootPacket_comm_1_4

theorem positiveRootAction_comm_3_4 (s t : Bool) :
    positiveRootAction 3 s * positiveRootAction 4 t =
      positiveRootAction 4 t * positiveRootAction 3 s := by
  cases s <;> cases t
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simpa [positiveRootAction] using positiveRootPacket_comm_3_4

theorem positiveRootAction_comm_3_5 (s t : Bool) :
    positiveRootAction 3 s * positiveRootAction 5 t =
      positiveRootAction 5 t * positiveRootAction 3 s := by
  cases s <;> cases t
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simpa [positiveRootAction] using positiveRootPacket_comm_3_5

theorem positiveRootAction_mul_0_2_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 0 s * positiveRootAction 2 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 0 then s else if i = 2 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_0_5_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 0 s * positiveRootAction 5 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 0 then s else if i = 5 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_1_4_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 1 s * positiveRootAction 4 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 1 then s else if i = 4 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_3_4_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 3 s * positiveRootAction 4 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 3 then s else if i = 4 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_3_5_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 3 s * positiveRootAction 5 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 3 then s else if i = 5 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_0_1_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 0 s * positiveRootAction 1 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 0 then s else if i = 1 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_1_2_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 1 s * positiveRootAction 2 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 1 then s else if i = 2 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_2_3_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 2 s * positiveRootAction 3 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 2 then s else if i = 3 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_4_5_mem_orderedRootProduct_range
    (s t : Bool) :
    positiveRootAction 4 s * positiveRootAction 5 t ∈
      Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 4 then s else if i = 5 then t else false, ?_⟩
  cases s <;> cases t <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_mul_0_1_2_mem_orderedRootProduct_range
    (s t u : Bool) :
    (positiveRootAction 0 s * positiveRootAction 1 t) *
        positiveRootAction 2 u ∈ Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 0 then s else if i = 1 then t else
    if i = 2 then u else false, ?_⟩
  cases s <;> cases t <;> cases u <;>
    simp [unipotentWord6, positiveRootAction]

theorem positiveRootAction_mul_mul_3_4_5_mem_orderedRootProduct_range
    (s t u : Bool) :
    (positiveRootAction 3 s * positiveRootAction 4 t) *
        positiveRootAction 5 u ∈ Set.range unipotentWord6 := by
  refine ⟨fun i => if i = 3 then s else if i = 4 then t else
    if i = 5 then u else false, ?_⟩
  cases s <;> cases t <;> cases u <;>
    simp [unipotentWord6, positiveRootAction]

theorem orderedRootProduct_range_subset_positiveRootSubgroup :
    Set.range unipotentWord6 ⊆ positiveRootSubgroup := by
  rintro _ ⟨b, rfl⟩
  exact unipotentWord6_mem_positiveRootSubgroup b

theorem positiveRootSubgroup_le_orderedRootProduct_closure :
    positiveRootSubgroup ≤
      Subgroup.closure (Set.range unipotentWord6) := by
  rw [positiveRootSubgroup]
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact Subgroup.subset_closure (positiveRootPacket_mem_orderedRootProduct_range i)

theorem positiveRootSubgroup_eq_orderedRootProduct_closure :
    positiveRootSubgroup =
      Subgroup.closure (Set.range unipotentWord6) := by
  apply le_antisymm
  · exact positiveRootSubgroup_le_orderedRootProduct_closure
  · rw [Subgroup.closure_le]
    exact orderedRootProduct_range_subset_positiveRootSubgroup

theorem nativeOrderedRootProduct_range_card :
    Nat.card (Set.range unipotentWord6) = 64 := by
  exact unipotentWord6_range_card

end InfoGeometry.Algebra.Zorn.G2NativeOrderedRootProduct
