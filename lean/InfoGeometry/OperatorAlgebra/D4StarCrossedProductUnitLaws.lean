import InfoGeometry.OperatorAlgebra.D4StarCrossedProductDistributiveLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Unit laws for the finite D₄ crossed-product convolution

The distinguished delta coefficient is a two-sided unit for the explicit
finite convolution.  This closes the unit part of the algebraic surface;
ring instances and normed completions remain separate declarations.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductUnitLaws

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

theorem crossedProductOne_mul
    (F : D4StarCrossedProduct) :
    crossedProductMul crossedProductOne F = F := by
  classical
  funext r v
  change
    (Finset.univ : Finset (Equiv.Perm InfoGeometry.Canonical.ColorChannel)).sum
        (fun g => (if g = 1 then 1 else 0) *
          colorPullback g (F.coeff (g.symm * r))) v = F r v
  rw [Finset.sum_eq_single 1]
  · simp [colorPullback_one]
  · intro b hb hne
    simp [hne]
  · simp

theorem crossedProductMul_one
    (F : D4StarCrossedProduct) :
    crossedProductMul F crossedProductOne = F := by
  classical
  funext r v
  change
    (Finset.univ : Finset (Equiv.Perm InfoGeometry.Canonical.ColorChannel)).sum
        (fun g => F.coeff g *
          colorPullback g (if g.symm * r = 1 then 1 else 0)) v = F r v
  rw [Finset.sum_eq_single r]
  · simp
  · intro b hb hne
    have hnot : b.symm * r ≠ 1 := by
      intro h
      apply hne
      symm
      calc
        r = (1 : Equiv.Perm InfoGeometry.Canonical.ColorChannel) * r := by simp
        _ = (b * b.symm) * r := by rw [Equiv.Perm.mul_symm]
        _ = b * (b.symm * r) := by rw [mul_assoc]
        _ = b * 1 := by rw [h]
        _ = b := by simp
    simp [hnot]
  · simp

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductUnitLaws
