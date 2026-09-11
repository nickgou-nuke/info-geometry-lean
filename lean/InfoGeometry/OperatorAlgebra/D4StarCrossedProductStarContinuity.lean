import InfoGeometry.OperatorAlgebra.D4StarCrossedProductFiniteDimensionalContinuity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topological continuity of the finite D₄ crossed-product involution

The finite coefficient carrier carries its canonical Pi topology.  This file
records continuity of the explicit involution; together with the existing
finite-dimensional continuity of left convolution, it gives a genuine
topological property for the noncommutative finite stage without installing a
completion or a commutative algebra instance.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarContinuity

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

theorem continuous_crossedProductStar :
    Continuous (crossedProductStar :
      D4StarCrossedProduct → D4StarCrossedProduct) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro v
  change Continuous (fun F : D4StarCrossedProduct =>
    (starRingEnd ℂ)
      (F r.symm (InfoGeometry.Topology.PauliJungD4Star.vertexPermutation
        r.symm v)))
  exact Complex.continuous_conj.comp
    ((continuous_apply
        (InfoGeometry.Topology.PauliJungD4Star.vertexPermutation r.symm v)).comp
      (continuous_apply r.symm))

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarContinuity
