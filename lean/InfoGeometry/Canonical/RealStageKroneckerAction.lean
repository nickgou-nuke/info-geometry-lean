import InfoGeometry.Canonical.RealStageMatrixAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealStageMatrixVectorReindex

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower

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
  fin_cases j <;>
    simp [realStageEmbeddedAction, realStageMatrixAction,
    stageVectorMatrixEquiv, matStageEmbed, Matrix.mulVecLin,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.kroneckerMap_apply,
    InfoGeometry.Clifford.TowerMatrix.Idx,
    Fintype.sum_prod_type, Finset.sum_mul]

end InfoGeometry.Canonical
