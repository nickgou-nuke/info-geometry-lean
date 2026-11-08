import InfoGeometry.Canonical.RealStageMatrixAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealStageMatrixVectorReindex

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower

/-- The recursive tensor index at the next stage is reindexed by its old
index and the new two-state factor. -/
def stageIdxSuccEquiv (n : ℕ) :
    InfoGeometry.Clifford.TowerMatrix.Idx (n + 1) ≃
      InfoGeometry.Clifford.TowerMatrix.Idx n × Fin 2 where
  toFun i := i
  invFun ij := ij
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem stageIdxSuccEquiv_symm_apply (n : ℕ)
    (ij : InfoGeometry.Clifford.TowerMatrix.Idx n × Fin 2) :
    (stageIdxSuccEquiv n).symm ij = ij := rfl

/-!
# The one-step tensor embedding on stage vectors

After reindexing a stage vector as a matrix with two columns, the action of
`A ⊗ₖ I₂` is ordinary left multiplication by `A` on those columns.  This is
the concrete finite-stage transport statement used by the dyadic tower.
-/

theorem stageEmbeddedAction_matrix_reindex
    (n : ℕ) (A : InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (X : StageBlockMatrix n) :
    (LinearEquiv.symm (stageVectorMatrixEquiv n))
        (realStageEmbeddedAction n A (stageVectorMatrixEquiv n X)) =
      A * X := by
  ext i j
  rw [stageVectorMatrixEquiv_symm_apply, realStageEmbeddedAction_apply]
  change (stageEmbed n A).mulVec (stageVectorMatrixEquiv n X)
    ((stageIdxSuccEquiv n).symm (i, j)) = _
  rw [Matrix.mulVec_apply_eq_sum]
  rw [Fintype.sum_equiv (stageIdxSuccEquiv n)
    (fun k => (stageEmbed n A) ((stageIdxSuccEquiv n).symm (i, j)) k *
      (stageVectorMatrixEquiv n X) k)
    (fun k => (stageEmbed n A) ((stageIdxSuccEquiv n).symm (i, j))
      ((stageIdxSuccEquiv n).symm k) *
      (stageVectorMatrixEquiv n X) ((stageIdxSuccEquiv n).symm k))
    (by intro k; rfl)]
  simp only [stageIdxSuccEquiv_symm_apply]
  simp [stageVectorMatrixEquiv, matStageEmbed, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  fin_cases j <;> simp <;> rfl

end InfoGeometry.Canonical
