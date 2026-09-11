import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

@[simp] theorem finiteChevalleyG2_mul_apply
    (f g : SplitOctF2Aut) (X : SplitOctF2) :
    (f * g : SplitOctF2Aut).1 X = g.1 (f.1 X) := rfl

@[simp] theorem finiteChevalleyG2_inv_apply
    (f : SplitOctF2Aut) (X : SplitOctF2) :
    (f⁻¹ : SplitOctF2Aut).1 X = f.1.symm X := rfl

theorem finite_chevalley_group_card_packet
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    Fintype.card SplitOctF2Aut =
      InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger.g2TwoOrder := by
  simpa [InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger.g2TwoOrder]
    using h_enum

end InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup

end noncomputable section
