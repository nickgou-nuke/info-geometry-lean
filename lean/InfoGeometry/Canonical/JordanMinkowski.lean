import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

namespace InfoGeometry.Canonical.JordanMinkowski

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- The Jordan product for elements of a Clifford Algebra -/
def jordanProduct {A : Type*} [Ring A] (u v : A) : A := u * v + v * u

/--
Theorem: The metric tensor (bilinear form) can be recovered from the Jordan product
structure of the Clifford algebra.
`e_i e_j + e_j e_i = 2 g_{ij}`
Here `g` is the polar bilinear form associated to the quadratic form `Q`.
-/
theorem jordan_recovers_metric (u v : M) :
    jordanProduct (CliffordAlgebra.ι Q u) (CliffordAlgebra.ι Q v) =
    algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q u v) := by
  exact CliffordAlgebra.ι_mul_ι_add_swap u v

end InfoGeometry.Canonical.JordanMinkowski
