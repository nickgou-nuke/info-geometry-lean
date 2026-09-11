import InfoGeometry.OperatorAlgebra.D4StarCrossedProductNonUnitalStarSurface
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Joint continuity of finite crossed-product convolution

The finite coefficient carrier has its native Pi topology.  Convolution is
therefore a continuous bilinear operation at this finite stage.  This is only
a topological statement; it does not install a completion or a C*-norm.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductMultiplicationContinuity

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.Topology.PauliJungD4Star
open InfoGeometry.Canonical

noncomputable section

theorem continuous_crossedProductMul :
    Continuous (fun p : D4StarCrossedProduct × D4StarCrossedProduct =>
      crossedProductMul p.1 p.2) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro v
  unfold crossedProductMul
  simp only [Finset.sum_apply]
  apply continuous_finset_sum
  intro g hg
  change Continuous (fun p : D4StarCrossedProduct × D4StarCrossedProduct =>
    p.1.coeff g v *
      (colorPullback g (p.2.coeff (g.symm * r))) v)
  have hF : Continuous (fun p : D4StarCrossedProduct × D4StarCrossedProduct =>
      p.1.coeff g v) :=
    (continuous_apply v).comp
      ((continuous_apply g).comp continuous_fst)
  have hK : Continuous (fun p : D4StarCrossedProduct × D4StarCrossedProduct =>
      (colorPullback g (p.2.coeff (g.symm * r))) v) := by
    simp only [colorPullback_apply]
    exact (continuous_apply (vertexPermutation g.symm v)).comp
      ((continuous_apply (g.symm * r)).comp continuous_snd)
  exact hF.mul hK

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductMultiplicationContinuity
