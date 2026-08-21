import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger

/-!
# Native finite Chevalley-group carrier for the `G₂(2)` lane

The existing finite Zorn carrier already defines the automorphism predicate.
This file supplies the missing group structure on that predicate.  The
cardinality `12096` remains a separate enumeration theorem: a group instance
does not, by itself, enumerate its elements.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

local notation "G2Two" => SplitOctF2Aut

private theorem comp_is_aut (f g : G2Two) :
    IsSplitOctF2Aut (f.1.trans g.1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact g.2.1 ▸ f.2.1
  · intro X Y
    rw [Equiv.trans_apply, g.2.2.1, f.2.2.1]
    exact (g.2.2.1 (f.1 X) (f.1 Y)).symm ▸ rfl
  · intro X Y
    rw [Equiv.trans_apply, g.2.2.2, f.2.2.2]
    exact (g.2.2.2 (f.1 X) (f.1 Y)).symm ▸ rfl

private theorem inv_is_aut (f : G2Two) :
    IsSplitOctF2Aut f.1.symm := by
  refine ⟨?_, ?_, ?_⟩
  · apply f.1.injective
    rw [f.1.apply_symm_apply, f.2.1, f.1.apply_symm_apply]
  · intro X Y
    apply f.1.injective
    rw [f.1.apply_symm_apply, f.2.2.1]
    simp only [f.1.apply_symm_apply]
  · intro X Y
    apply f.1.injective
    rw [f.1.apply_symm_apply, f.2.2.2]
    simp only [f.1.apply_symm_apply]

instance : Group G2Two where
  one := ⟨Equiv.refl SplitOctF2, by
    refine ⟨?_, ?_, ?_⟩ <;> simp⟩
  mul f g := ⟨f.1.trans g.1, comp_is_aut f g⟩
  inv f := ⟨f.1.symm, inv_is_aut f⟩
  one_mul f := by ext X; rfl
  mul_one f := by ext X; rfl
  mul_assoc f g h := by ext X; rfl
  mul_left_inv f := by ext X; exact f.1.symm_apply_apply X

@[simp] theorem coe_mul (f g : G2Two) (X : SplitOctF2) :
    ((f * g : G2Two) : SplitOctF2 ≃ SplitOctF2) X = g.1 (f.1 X) :=
  rfl

@[simp] theorem coe_inv (f : G2Two) (X : SplitOctF2) :
    ((f⁻¹ : G2Two) : SplitOctF2 ≃ SplitOctF2) X = f.1.symm X :=
  rfl

theorem finite_chevalley_group_card_packet
    (h_enum : Fintype.card G2Two = 12096) :
    Fintype.card G2Two =
      InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger.g2TwoOrder := by
  simpa [InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger.g2TwoOrder]
    using h_enum

end InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup

end noncomputable section
