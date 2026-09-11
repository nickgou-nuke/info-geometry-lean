import InfoGeometry.Canonical.ManifoldDegreeCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.DualFlat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# InfoGeometry.Canonical.ManifoldDegreeIntegration

Bridge between mapping degree and volume-form integrals on information manifolds.
Links the topological degree sum to the integral of the pullback volume form.
-/

namespace InfoGeometry.Canonical.ManifoldDegree

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
variable [MeasurableSpace M] [TopologicalSpace M] [BorelSpace M]

/--
The Change of Variables formula for the mapping degree:
The integral of the pullback of a volume form `ω` is the degree times the integral of `ω`.
In Hessian geometry, `ω` is the Monge-Ampère density.
-/
def degree_change_of_variables_formula
    (f : M → M) (μ : MeasureTheory.Measure M)
    [MeasureTheory.IsFiniteMeasure μ]
    (y : M) (hy : ManifoldHomology.IsRegularValue f y)
    (hfinite : (f ⁻¹' ({y} : Set M)).Finite)
    (deg : ℤ := mappingDegree f y hy hfinite) :
    Prop :=
  ∀ (ω : M → ℝ), (∫ x, (localDegreeSign f x : ℝ) * ω (f x) ∂μ) = (deg : ℝ) * (∫ x, ω x ∂μ)

end InfoGeometry.Canonical.ManifoldDegree
