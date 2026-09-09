import InfoGeometry.Categorical.LogNilpotentCrossCheckedR

/-!
# Zero-parameter boundary of the logarithmic checked `R`

The cross-checked construction has a genuine canonical boundary at `p = 0`:
the nilpotent shear disappears and the operator is exactly the Mathlib tensor
symmetry.  This small owner records the boundary without asserting a
Yang--Baxter identity for the nonzero shear parameter.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentCrossCheckedR

open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory

variable (X : LogNilpotentModule ℂ)
variable (hX : X.N ^ 2 = 0)

theorem logCheckedR_zero :
    logCheckedR X hX 0 = TensorProduct.comm ℂ X X := by
  ext t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x y
    simp [logCheckedR_tmul]
  · intro a b ha hb
    simp [map_add, ha, hb]

end InfoGeometry.Categorical.LogNilpotentCrossCheckedR
