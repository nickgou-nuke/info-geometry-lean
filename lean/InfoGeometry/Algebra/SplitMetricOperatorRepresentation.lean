import InfoGeometry.Algebra.EquivariantProjectorRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitMetricSpace

/-!
# Metric operator representations

This contract attaches a representation to the canonical split metric.  It is
the point at which a Clifford or Peirce operator basis becomes a split-metric
realization: every represented Lie operator must be skew for the same
nondegenerate symmetric form.
-/

namespace InfoGeometry.Algebra

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

structure SplitMetricOperatorRepresentation
    (K : DerivationLieLane R A) (S : SplitMetricSpace R) where
  rho : K.L →ₗ⁅R⁆ Module.End R S.V
  metric_skew : ∀ x u v,
    S.beta (rho x u) v + S.beta u (rho x v) = 0

namespace SplitMetricOperatorRepresentation

variable {K : DerivationLieLane R A} {S : SplitMetricSpace R}

theorem preserves_metric
    (ρ : SplitMetricOperatorRepresentation K S) (x : K.L) (u v : S.V) :
    S.beta (ρ.rho x u) v = -S.beta u (ρ.rho x v) := by
  exact eq_neg_of_add_eq_zero_left (ρ.metric_skew x u v)

end SplitMetricOperatorRepresentation

end InfoGeometry.Algebra
