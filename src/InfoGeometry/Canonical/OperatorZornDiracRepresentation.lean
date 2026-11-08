import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Faithful matrix representation of the operator-Zorn block carrier

The operator-valued four-slot carrier is already transported from ordinary
`2 × 2` matrices in `OperatorZornMatrixAlgebra`.  This owner exposes that
transport as an explicit ring homomorphism and records its faithfulness and
star covariance.  No physical Dirac interpretation is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.OperatorZornDiracRepresentation

open InfoGeometry.Physics.OperatorZornMatrix
open InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

abbrev Carrier (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Physics.OperatorZornMatrix A
abbrev DiracBlocks (A : Type*) := Mat2 A

def zornDiracRepresentation (A : Type*) [Ring A] [StarRing A] :
    Carrier A →+* DiracBlocks A where
  toFun := equivMatrix
  map_one' := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  map_zero' := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' := by
    intro M N
    change equivMatrix (M + N) = equivMatrix M + equivMatrix N
    simpa only [Equiv.add_def, equivMatrix_apply, equivMatrix_symm_apply,
      toMatrix_ofMatrix]
  map_mul' := by
    intro M N
    change equivMatrix (M * N) = equivMatrix M * equivMatrix N
    simpa only [Equiv.mul_def, equivMatrix_apply, equivMatrix_symm_apply,
      toMatrix_ofMatrix]

@[simp] theorem zornDiracRepresentation_apply (M : Carrier A) :
    zornDiracRepresentation A M = equivMatrix M := rfl

theorem zornDiracRepresentation_injective :
    Function.Injective (zornDiracRepresentation A) := by
  exact equivMatrix.injective

theorem zornDiracRepresentation_star (M : Carrier A) :
    zornDiracRepresentation A (star M) = star (zornDiracRepresentation A M) := by
  exact toMatrix_starOp M

theorem zornDiracRepresentation_mul (M N : Carrier A) :
    zornDiracRepresentation A (M * N) =
      zornDiracRepresentation A M * zornDiracRepresentation A N := by
  exact map_mul (zornDiracRepresentation A) M N

theorem zornDiracRepresentation_add (M N : Carrier A) :
    zornDiracRepresentation A (M + N) =
      zornDiracRepresentation A M + zornDiracRepresentation A N := by
  exact map_add (zornDiracRepresentation A) M N

end InfoGeometry.Canonical.OperatorZornDiracRepresentation
