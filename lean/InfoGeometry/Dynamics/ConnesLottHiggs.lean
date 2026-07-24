import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Canonical.CuntzUHFAlgebra
import InfoGeometry.Canonical.PrimitiveCuntzIsometry
import InfoGeometry.Canonical.PrimitiveCuntzCohomology

noncomputable section

namespace InfoGeometry.Dynamics.ConnesLott

open Complex
open InfoGeometry.GrandUnification.UHF
open InfoGeometry.Canonical.PrimitiveCuntzIsometry
open InfoGeometry.Canonical.PrimitiveCuntzCohomology

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
variable [UHF : UHFAlgebra A]

/--
The boundary transition element between the two Cuntz branches.

The name is only a Connes--Lott-inspired finite algebraic readout; this file
does not construct a physical Higgs field.
-/
def connesLottBoundaryField : A := UHF_boundary (A := A)

/--
The boundary transition element squares to zero.
-/
theorem connesLottBoundaryField_sq_zero :
    connesLottBoundaryField (A := A) * connesLottBoundaryField (A := A) = 0 := by
  -- Follows identically from UHF_boundary_sq_eq_zero
  exact UHF_boundary_sq_eq_zero

/--
The boundary transition and its adjoint satisfy the exact UHF Laplacian identity.
This is not a Yang--Mills or Higgs mass-gap theorem.
-/
theorem connesLottBoundaryField_laplacian_eq_one :
    connesLottBoundaryField (A := A) * star (connesLottBoundaryField (A := A)) +
    star (connesLottBoundaryField (A := A)) * connesLottBoundaryField (A := A) = 1 := by
  -- This is structurally the exact UHF Laplacian
  exact UHF_Laplacian_eq_one

/--
The boundary transition maps a right-supported expression to the corresponding
left-right expression by the Cuntz isometry law.
-/
theorem connesLottBoundaryField_chiral_crossing (X : A) :
    connesLottBoundaryField (A := A) * (UHFAlgebra.S_R (A := A) * X * star (UHFAlgebra.S_R (A := A))) =
    UHFAlgebra.S_L (A := A) * X * star (UHFAlgebra.S_R (A := A)) := by
  dsimp [connesLottBoundaryField, UHF_boundary]
  calc
    (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) * (UHFAlgebra.S_R (A := A) * X * star (UHFAlgebra.S_R (A := A)))
      = UHFAlgebra.S_L (A := A) * (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_R (A := A)) * X * star (UHFAlgebra.S_R (A := A)) := by simp [mul_assoc]
    _ = UHFAlgebra.S_L (A := A) * 1 * X * star (UHFAlgebra.S_R (A := A)) := by rw [UHFAlgebra.isometry_R]
    _ = UHFAlgebra.S_L (A := A) * X * star (UHFAlgebra.S_R (A := A)) := by simp

end InfoGeometry.Dynamics.ConnesLott
