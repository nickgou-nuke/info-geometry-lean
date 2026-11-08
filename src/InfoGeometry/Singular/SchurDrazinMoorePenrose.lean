import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Singular.SchurDrazinMoorePenrose

Closed algebraic core for Schur/Drazin/Moore--Penrose readbacks.
-/

noncomputable section

namespace InfoGeometry.Singular.SchurDrazinMoorePenrose

section Ring

variable {R : Type*} [Ring R]

/-- Drazin regular block readback: `A D A`. -/
def drazinRegularBlock (A D : R) : R :=
  A * D * A

/-- Drazin nilpotent/residue block readback: `A - A D A`. -/
def drazinResidueBlock (A D : R) : R :=
  A - drazinRegularBlock A D

/-- The regular and residue blocks add back to the original operator. -/
theorem drazinRegular_add_residue (A D : R) :
    drazinRegularBlock A D + drazinResidueBlock A D = A := by
  simp [drazinRegularBlock, drazinResidueBlock]

/-- The residue block is definitionally the Schur complement shadow used here. -/
theorem drazinResidueBlock_eq (A D : R) :
    drazinResidueBlock A D = A - A * D * A := by
  rfl

end Ring

end InfoGeometry.Singular.SchurDrazinMoorePenrose
