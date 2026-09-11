import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace Automath.Generated

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous bilinear form representing either an entropy Hessian or an
inverse information metric on the thermodynamic parameter space `E`. -/
abbrev ThermodynamicBilinearForm (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

/--
The Hessian of the Massieu/entropy potential equals the inverse of the
Souriau–Fisher information metric.
-/
theorem entropyHessian_eq_fisherInverse
    (entropyHessian fisherInverse : ThermodynamicBilinearForm E)
    (hIdentification :
      ∀ x y : E, entropyHessian x y = fisherInverse x y) :
    entropyHessian = fisherInverse := by
  ext x y
  exact hIdentification x y

end Automath.Generated
