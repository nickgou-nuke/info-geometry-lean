import InfoGeometry.Algebra.Zorn.G2TwoUnipotentStructure
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2UnipotentWord6Cardinality

open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!
# Cardinality of the ordered six-bit word range

This owner records exactly what the coordinate-separator theorem provides:
the ordered word map has a 64-element range.  It deliberately does not
identify that range with a residual or root subgroup.
-/

theorem unipotentWord6_range_card_of_coordinate_separators
    (h0 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up1).x0 = b 0)
    (h1 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down1).y2 = b 1)
    (h2 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up2).x0 = b 2)
    (h3 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y0 = b 3)
    (h4 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up0).x1 = b 4)
    (h5 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y1 = b 5) :
    Nat.card (Set.range unipotentWord6) = 64 := by
  let h_inj : Function.Injective unipotentWord6 :=
    unipotentWord6_injective_of_coordinate_separators h0 h1 h2 h3 h4 h5
  let e : (Fin 6 → Bool) ≃ Set.range unipotentWord6 :=
    Equiv.ofInjective unipotentWord6 h_inj
  rw [← Nat.card_congr e]
  simp

theorem unipotentWord6_up1_x0_readback :
    ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up1).x0 = b 0 := by
  decide

theorem unipotentWord6_down1_y2_readback :
    ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down1).y2 = b 1 := by
  decide

theorem unipotentWord6_up2_x0_readback :
    ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up2).x0 = b 2 := by
  decide

theorem unipotentWord6_down2_y0_readback :
    ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y0 = b 3 := by
  decide

theorem unipotentWord6_up0_x1_readback :
    ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up0).x1 = b 4 := by
  decide

theorem unipotentWord6_down2_y1_readback :
    ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y1 = b 5 := by
  decide

theorem unipotentWord6_range_card :
    Nat.card (Set.range unipotentWord6) = 64 := by
  exact unipotentWord6_range_card_of_coordinate_separators
    unipotentWord6_up1_x0_readback
    unipotentWord6_down1_y2_readback
    unipotentWord6_up2_x0_readback
    unipotentWord6_down2_y0_readback
    unipotentWord6_up0_x1_readback
    unipotentWord6_down2_y1_readback

theorem positiveRootSubgroup_card_ge_64_of_coordinate_separators
    (h0 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up1).x0 = b 0)
    (h1 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down1).y2 = b 1)
    (h2 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up2).x0 = b 2)
    (h3 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y0 = b 3)
    (h4 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up0).x1 = b 4)
    (h5 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y1 = b 5) :
    64 ≤ Fintype.card positiveRootSubgroup := by
  let f : (Fin 6 → Bool) → positiveRootSubgroup := fun b =>
    ⟨unipotentWord6 b, unipotentWord6_mem_positiveRootSubgroup b⟩
  have hf : Function.Injective f := by
    intro b c h
    apply unipotentWord6_injective_of_coordinate_separators h0 h1 h2 h3 h4 h5
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

theorem positiveRootSubgroup_card_ge_64 :
    64 ≤ Fintype.card positiveRootSubgroup := by
  exact positiveRootSubgroup_card_ge_64_of_coordinate_separators
    unipotentWord6_up1_x0_readback
    unipotentWord6_down1_y2_readback
    unipotentWord6_up2_x0_readback
    unipotentWord6_down2_y0_readback
    unipotentWord6_up0_x1_readback
    unipotentWord6_down2_y1_readback

end InfoGeometry.Algebra.Zorn.G2UnipotentWord6Cardinality
