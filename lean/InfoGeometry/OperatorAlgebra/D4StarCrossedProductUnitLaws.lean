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
  · simp [colorPullback_apply,
      InfoGeometry.Topology.PauliJungD4Star.vertexPermutation,
      Equiv.Perm.one_symm]
    cases v <;> rfl
  · intro b hb hne
    funext v
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ 1))

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
  · change F.coeff r v *
      colorPullback r (if r.symm * r = 1 then 1 else 0) v = F.coeff r v
    have hr : r.symm * r = 1 := by
      rw [Equiv.Perm.symm_mul]
    rw [if_pos hr]
    rw [colorPullback_apply]
    simp
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
