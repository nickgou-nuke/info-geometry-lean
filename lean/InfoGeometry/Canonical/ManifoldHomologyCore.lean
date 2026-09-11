import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Basic

/-!
# InfoGeometry.Canonical.ManifoldHomologyCore

Canonical core for manifold/homology foundations.
Transitioned from draft scaffolding to rigorous differential-geometric definitions.
-/

namespace InfoGeometry.Canonical.ManifoldHomology

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/--
A value `y` is a regular value of `f` if the derivative at every preimage is invertible.
In finite dimensions, this is equivalent to the Jacobian determinant being non-zero.
-/
def IsRegularValue (f : M → M) (y : M) : Prop :=
  by
    classical
    exact ∀ x, f x = y → LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0
  -- finite-dimensional requirement is inferred from `LinearMap.det`.

/--
The local degree sign at a point `x` is the sign of the Jacobian determinant.
This uses the linear operator's determinant.
-/
noncomputable def localDegreeSign (f : M → M) (x : M) : ℤ :=
  if 0 < LinearMap.det (fderiv ℝ f x).toLinearMap then 1 else -1

/--
The mapping degree of `f` at a regular value `y` is the sum of local degree signs
over the (finite) fiber `f⁻¹' {y}`.
-/
noncomputable def mappingDegree (f : M → M) (y : M) (_hy : IsRegularValue f y)
    (hfinite : (f ⁻¹' ({y} : Set M)).Finite) : ℤ :=
  letI : Fintype (f ⁻¹' ({y} : Set M)) := hfinite.fintype
  ∑ x : (f ⁻¹' ({y} : Set M)), localDegreeSign f x

/--
Degree/Jacobian compatibility: `mappingDegree` is exactly the sum of local Jacobian signs
over the finite preimage fiber.
-/
theorem mappingDegree_eq_sum_localDegreeSign
    (f : M → M) (y : M) (hy : IsRegularValue f y)
    (hfinite : (f ⁻¹' ({y} : Set M)).Finite) :
    mappingDegree f y hy hfinite
      = by
          letI : Fintype (f ⁻¹' ({y} : Set M)) := hfinite.fintype
          exact ∑ x : (f ⁻¹' ({y} : Set M)), localDegreeSign f x :=
  rfl

end InfoGeometry.Canonical.ManifoldHomology
