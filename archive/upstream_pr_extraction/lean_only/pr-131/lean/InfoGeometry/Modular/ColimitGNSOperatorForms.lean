import InfoGeometry.Modular.ColimitGNS
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra

/-!
# GNS expectation readouts of operator-valued two-forms

This file only performs the existing algebraic readout.  It does not assert
that a BKM state is a colimit GNS state; such a comparison requires an
explicit state-preserving morphism.
-/

noncomputable section

namespace InfoGeometry.Modular.ColimitGNSOperatorForms

open InfoGeometry.Modular.ColimitGNS
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

variable {A V : Type*}
  [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [AddCommGroup V] [Module ℂ V]

/-- Expectation of an operator-valued alternating two-form in a GNS state. -/
def gnsTwoFormExpectation
    (ω : GNSState A) (κ : Op2Form ℂ V A) (u v : V) : ℂ :=
  ω (κ u v)

theorem gnsTwoFormExpectation_skew
    (ω : GNSState A) (κ : Op2Form ℂ V A) (u v : V) :
    gnsTwoFormExpectation ω κ u v =
      - gnsTwoFormExpectation ω κ v u := by
  unfold gnsTwoFormExpectation
  rw [κ.skew]
  exact ω.toLinearMap.map_neg (κ v u)

theorem gnsTwoFormExpectation_wedge_self
    (ω : GNSState A) (α : Op1Form ℂ V A) (u v : V) :
    gnsTwoFormExpectation ω (wedge α α) u v =
      ω (α u * α v - α v * α u) := by
  rfl

end InfoGeometry.Modular.ColimitGNSOperatorForms

end noncomputable section
