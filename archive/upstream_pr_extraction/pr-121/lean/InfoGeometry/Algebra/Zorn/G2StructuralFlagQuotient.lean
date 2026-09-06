import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Card

/-!
# Structural quotient-to-flag transport

This module isolates the generic orbit--stabilizer step used by the concrete
`G₂(2)` flag classification.  The concrete action, transitivity, and
stabilizer identification remain explicit obligations; no ambient cardinality
is used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient

variable {G X : Type*} [Group G] [MulAction G X]

noncomputable def orbitToTarget (x : X)
    (h_surj : Function.Surjective (fun g : G => g • x)) :
    MulAction.orbit G x ≃ X :=
  Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, by
      intro y
      obtain ⟨g, rfl⟩ := h_surj y
      exact ⟨⟨g • x, ⟨g, rfl⟩⟩, rfl⟩⟩

noncomputable def quotientStabilizerFlagEquiv (x : X)
    (h_surj : Function.Surjective (fun g : G => g • x)) :
    (G ⧸ MulAction.stabilizer G x) ≃ X :=
  (MulAction.orbitEquivQuotientStabilizer G x).symm.trans
    (orbitToTarget x h_surj)

theorem quotientStabilizerFlagEquiv_apply (x : X)
    (h_surj : Function.Surjective (fun g : G => g • x)) (g : G) :
    quotientStabilizerFlagEquiv x h_surj (QuotientGroup.mk g) = g • x := by
  exact MulAction.ofQuotientStabilizer_mk G x g

noncomputable def quotientFlagEquivOfStabilizerEq (x : X) (H : Subgroup G)
    (h_stab : MulAction.stabilizer G x = H)
    (h_surj : Function.Surjective (fun g : G => g • x)) :
    (G ⧸ H) ≃ X := by
  rw [← h_stab]
  exact quotientStabilizerFlagEquiv x h_surj

theorem quotient_card_of_stabilizer_eq [Fintype G] [Fintype X]
    (x : X) (H : Subgroup G) [Fintype (G ⧸ H)]
    (h_stab : MulAction.stabilizer G x = H)
    (h_surj : Function.Surjective (fun g : G => g • x)) :
    Fintype.card (G ⧸ H) = Fintype.card X := by
  exact Fintype.card_congr (quotientFlagEquivOfStabilizerEq x H h_stab h_surj)

end InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient
