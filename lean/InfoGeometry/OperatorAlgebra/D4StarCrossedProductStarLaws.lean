import InfoGeometry.OperatorAlgebra.D4StarCrossedProductAlgebraicSurface
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Star multiplicativity for the finite D₄ crossed-product convolution

This owner closes the anti-multiplicativity law of the explicit finite
convolution involution.  It is proved by finite-group reindexing and the
equivariance of `colorPullback`; no completion is involved.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarLaws

open scoped BigOperators
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

theorem crossedProductStar_mul
    (F K : D4StarCrossedProduct) :
    crossedProductStar (crossedProductMul F K) =
      crossedProductMul (crossedProductStar K) (crossedProductStar F) := by
  classical
  funext r
  simp only [crossedProductStar, crossedProductMul]
  rw [star_sum]
  simp only [star_mul]
  rw [map_sum]
  simp only [map_mul, map_star]
  rw [← (Equiv.mulLeft r.symm).sum_comp]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Equiv.coe_mulLeft]
  ext v
  have hmul₁ : (r.symm * g).symm = g.symm * r := by
    change (r.symm * g)⁻¹ = g⁻¹ * r
    exact mul_inv_rev r.symm g
  have hmul₂ : (g.symm * r).symm = r.symm * g := by
    change (g.symm * r)⁻¹ = r⁻¹ * g
    exact mul_inv_rev g.symm r
  have hleft : (r.symm * g).symm * r.symm = g.symm := by
    rw [hmul₁, mul_assoc, Equiv.Perm.mul_symm, mul_one]
  have hright : (g.symm * r).symm = r.symm * g := hmul₂
  rw [hleft, hright]
  cases v <;>
    simp [colorPullback, InfoGeometry.Topology.PauliJungD4Star.vertexPermutation,
      Equiv.Perm.mul_def, Equiv.trans_apply, mul_inv_rev, mul_assoc]
  · intro a ha
    exact Finset.mem_univ a

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarLaws
