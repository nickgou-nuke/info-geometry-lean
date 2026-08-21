import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import Mathlib.Tactic

/-!
# A certified lower bound for the concrete simple-root subgroup

The two already certified involutions yield eight distinct subgroup elements.
This owner records the resulting lower bound only.  An exact order theorem
requires a separately proved normal-form reduction and is intentionally not
asserted here.
-/

namespace InfoGeometry.Algebra.Zorn.G2Unipotent

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem simpleRootSubgroup_card_ge_eight :
    8 ≤ Fintype.card simpleRootSubgroup :=
  simpleRootSubgroup_card_lower_bound_eight

/-- The two concrete involutions invert their product by conjugation. -/
theorem simpleRootProduct_conjugate_inverse :
    unipotentShortAut true *
        (unipotentShortAut true * unipotentLongAut true) *
        unipotentShortAut true =
      (unipotentShortAut true * unipotentLongAut true)⁻¹ := by
  rw [mul_assoc, unipotentShortAut_order true, one_mul]
  rw [mul_inv_rev, unipotentShortAut_inv, unipotentLongAut_inv]


end InfoGeometry.Algebra.Zorn.G2Unipotent
