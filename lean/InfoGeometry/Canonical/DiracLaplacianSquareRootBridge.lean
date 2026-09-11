import InfoGeometry.Canonical.DiracMetricCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

/-!
# Dirac--Laplacian square-root readout

This is a small public adapter around the existing `DiracMetricCompatibility`
owner.  The repository already proves two separate facts: Dirac--Kähler
operators square to their Hodge Laplacian, and the positive square root of a
finite-dimensional symmetric nonnegative metric operator is canonical.  This
file exposes the latter fact as a reusable square-root API and gives the
conditional identification with any supplied Laplacian operator.

No differential or unbounded operator is introduced here.  The equality with a
Laplacian is therefore explicit data (`hMetric`), rather than an unsupported
claim that every metric operator is a geometric Laplacian.
-/

namespace InfoGeometry.Canonical.DiracLaplacianSquareRootBridge

open InfoGeometry.Canonical
open InfoGeometry.Convex

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

section

variable (H : HessianGeometry E) (x₀ : E)

/-- The canonical positive Dirac operator squares to the Hessian metric operator. -/
theorem canonicalDirac_sq_eq_metricOp :
    DiracMetricCompatibility.canonicalDiracOfMetric (E := E) H x₀ *
        DiracMetricCompatibility.canonicalDiracOfMetric (E := E) H x₀ =
      H.metricOp x₀ := by
  exact (DiracMetricCompatibility.ofMetric (E := E) H x₀).dirac_sq_eq_metric

/--
If a supplied operator is identified with the Hessian metric operator, the
canonical positive Dirac operator is a square root of that operator as well.
-/
theorem canonicalDirac_sq_eq_laplacian
    (Δ : E →L[ℝ] E) (hMetric : H.metricOp x₀ = Δ) :
    DiracMetricCompatibility.canonicalDiracOfMetric (E := E) H x₀ *
        DiracMetricCompatibility.canonicalDiracOfMetric (E := E) H x₀ = Δ := by
  rw [canonicalDirac_sq_eq_metricOp (E := E) H x₀, hMetric]

/-- The canonical square root is positive in the metric-induced sense. -/
theorem canonicalDirac_isPositive :
    (DiracMetricCompatibility.canonicalDiracOfMetric (E := E) H x₀).IsPositive := by
  exact DiracMetricCompatibility.canonicalDiracOfMetric_isPositive (E := E) H x₀
    (H.metricOp_isSymmetric x₀) (fun u => H.metric_quadratic_nonneg x₀ u)

end

end InfoGeometry.Canonical.DiracLaplacianSquareRootBridge
