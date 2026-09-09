import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Card
import InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient

/-!
# Quotient transport for the G2 Flag Equivalence

This module provides the quotient-to-flag equivalence interface for `G₂(2)`.
It delegates the generic orbit-stabilizer construction to `G2StructuralFlagQuotient`.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientFlagEquiv

open InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient

variable {G X : Type*} [Group G] [MulAction G X]

/-- The orbit-stabilizer equivalence between the coset space `G ⧸ Stab(x)` and the flag target `X`. -/
noncomputable def quotientFlagEquiv (x : X)
    (h_surj : Function.Surjective (fun g : G => g • x)) :
    (G ⧸ MulAction.stabilizer G x) ≃ X :=
  quotientStabilizerFlagEquiv x h_surj

/-- Cardinality transfer from the quotient space to the flag target. -/
theorem flag_card_from_quotient [Fintype G] [Fintype X]
    (x : X) (H : Subgroup G) [Fintype (G ⧸ H)]
    (h_stab : MulAction.stabilizer G x = H)
    (h_surj : Function.Surjective (fun g : G => g • x)) :
    Fintype.card (G ⧸ H) = Fintype.card X :=
  quotient_card_of_stabilizer_eq x H h_stab h_surj

end InfoGeometry.Algebra.Zorn.G2QuotientFlagEquiv
