import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Covariance property for the finite D₄ crossed-product carrier

The finite crossed-product carrier retains the triality action through the
covariance relation between a group unitary and an outer-vertex projection.
This is a coefficient-level statement; it does not install a completion or
claim a universal C*-crossed-product construction.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductCovariance

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

theorem groupUnitary_mul_outerProjection_eq_outerProjection_mul_groupUnitary
    (σ : Equiv.Perm InfoGeometry.Canonical.ColorChannel)
    (c : InfoGeometry.Canonical.ColorChannel) :
    groupUnitary σ * observableEmbedding (outerProjection c) =
      observableEmbedding (outerProjection (σ c)) * groupUnitary σ := by
  ext r
  by_cases hr : r = σ
  · subst r
    simp only [groupUnitary_mul_observableEmbedding_coeff,
      observableEmbedding_mul_groupUnitary_coeff, if_pos rfl]
    change colorPullback σ (outerProjection c) _ = _
    exact congrFun (colorPullback_outerProjection σ c) _
  · simp [groupUnitary_mul_observableEmbedding_coeff,
      observableEmbedding_mul_groupUnitary_coeff, hr]

theorem covariance_is_nontrivial_of_moved_outer
    (σ : Equiv.Perm InfoGeometry.Canonical.ColorChannel)
    (c : InfoGeometry.Canonical.ColorChannel)
    (hmove : σ c ≠ c) :
    groupUnitary σ * observableEmbedding (outerProjection c) ≠
      observableEmbedding (outerProjection c) * groupUnitary σ :=
  crossedProduct_noncommutative σ c hmove

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductCovariance
