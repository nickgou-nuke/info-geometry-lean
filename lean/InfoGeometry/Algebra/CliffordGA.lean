import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace InfoGeometry.Algebra.CliffordGA

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- 
The core universal property of the Clifford Algebra:
The square of a basis vector equals the quadratic form evaluated on it.
This corresponds to the `e_i^2 = Q(e_i)` relation verified in SGAE/galgebra.
-/
theorem clifford_square_eq_quadratic_form (m : M) :
    (ι Q m) * (ι Q m) = algebraMap R (CliffordAlgebra Q) (Q m) := by
  exact ι_sq_scalar Q m

end InfoGeometry.Algebra.CliffordGA
