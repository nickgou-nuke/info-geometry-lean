import InfoGeometry.Algebra.SplitMetricLieAlgebra
import InfoGeometry.Canonical.CanonicalZornMatrixMetric

namespace CanonicalZornFiveGradedClosure

open InfoGeometry.Algebra

noncomputable def canonicalZornOrthogonalLie :
    SplitMetricLieAlgebra ℂ canonicalZornMetric where
  L := skewAdjointLieSubalgebra canonicalZornMetric.beta
  addCommGroup := inferInstance
  module := inferInstance
  lieRing := inferInstance
  lieAlgebra := inferInstance
  toSkewEnd := LinearMap.id
  bracket_eq_commutator := by intro x y; rfl
  toSkewEnd_injective := Function.injective_id

end CanonicalZornFiveGradedClosure
