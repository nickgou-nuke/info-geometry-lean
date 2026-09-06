import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Liquidation of Open Closure Debt: Parity Preservation and Vector Relations
This file contains the native, closed proofs for Bucket C items, eliminating 
`sorry` tokens from the conformal subalgebra without introducing new wrappers.
-/

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (Q : QuadraticForm R V)

local notation "Cl" => CliffordAlgebra Q

namespace ConformalSubalgebra

/-- The grading automorphism (grade-reversal) operator θ on the Clifford Algebra. -/
def thetaOp (x : Cl) : Cl := CliffordAlgebra.involute x

/-- Compatibility alias for the older local naming used in the project notes. -/
@[simp] theorem gradeInvol_eq_involute (x : Cl) : CliffordAlgebra.involute x = thetaOp (Q := Q) x := by
  rfl

/-- Lemma 1: Parity preservation of the product of two orthogonal Clifford vectors.
   This liquidates the debt for `J_even` and provides the witness for `thetaOpEven`. -/
theorem even_product_of_vectors (u v : V) :
    CliffordAlgebra.involute (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v := by
  -- θ is an algebra homomorphism, distribute over multiplication
  rw [map_mul]
  -- θ maps every 1-vector to its negative
  rw [CliffordAlgebra.involute_ι, CliffordAlgebra.involute_ι]
  -- Simplify (-a) * (-b) = a * b in the underlying non-commutative ring
  rw [neg_mul_neg]

/-- Lemma 2: Linear map derivation property for the dilation adjoint action.
    Natively proves the algebraic step for `adD_mul` expansions without placeholders. -/
theorem ad_derivation_step (d a b : Cl) :
    (d * (a * b) - (a * b) * d) = (d * a - a * d) * b + a * (d * b - b * d) := by
  -- Expand the right hand side via non-commutative ring axioms
  rw [sub_mul, mul_sub]
  -- Associate products to match the structure
  rw [mul_assoc, mul_assoc d a b, ← mul_assoc a d b]
  -- Add and subtract the intertwining token (a * d * b) to close the ring identity
  abel

/-- Lemma 3: Universal sign inversion relation under internal reflection conjugation.
    If J is an invertible element such that J^2 = -1, the conjugation action matches θ. -/
theorem reflection_conjugation_sq_neg_one (J x : Cl) (hJ : J * J = -1) (hx : J * x = - x * J) :
    J * x * J = x := by
  -- normalize anti-commutation witness to `-(x * J)`
  have hx' : J * x = - (x * J) := by
    simpa [neg_mul] using hx
  calc
    J * x * J = (J * x) * J := by rfl
    _ = (-(x * J)) * J := by
      exact congrArg (fun y => y * J) hx'
    _ = -((x * J) * J) := by rw [neg_mul]
    _ = -(x * (J * J)) := by rw [mul_assoc]
    _ = -(x * -1) := by rw [hJ]
    _ = x := by simp

end ConformalSubalgebra