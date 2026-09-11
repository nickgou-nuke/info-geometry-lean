import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford

/-!
# Reindexing stage vectors as rectangular matrices

The tensor-tower stage `Idx (n + 1)` is definitionally a product
`Idx n × Fin 2`.  This owner records the elementary linear equivalence
between functions on that product and rectangular matrices.  It is a
carrier-level bridge only; no Kronecker action is asserted here.
-/

abbrev StageVector (n : ℕ) := TowerMatrix.Idx n → ℝ

abbrev StageBlockMatrix (n : ℕ) := Matrix (TowerMatrix.Idx n) (Fin 2) ℝ

def stageVectorMatrixEquiv (n : ℕ) :
    StageBlockMatrix n ≃ₗ[ℝ] StageVector (n + 1) where
  toFun M := fun ij => M ij.1 ij.2
  invFun f := fun i j => f (i, j)
  left_inv M := by
    funext i j
    rfl
  right_inv f := by
    funext ij
    cases ij
    rfl
  map_add' M N := by
    funext ij
    rfl
  map_smul' c M := by
    funext ij
    rfl

@[simp] theorem stageVectorMatrixEquiv_apply
    (n : ℕ) (M : StageBlockMatrix n) (i : TowerMatrix.Idx n) (j : Fin 2) :
    stageVectorMatrixEquiv n M (i, j) = M i j := rfl

@[simp] theorem stageVectorMatrixEquiv_symm_apply
    (n : ℕ) (f : StageVector (n + 1))
    (i : TowerMatrix.Idx n) (j : Fin 2) :
    (stageVectorMatrixEquiv n).symm f i j = f (i, j) := rfl

theorem stageVectorMatrixEquiv_apply_pair
    (n : ℕ) (M : StageBlockMatrix n) (ij : TowerMatrix.Idx (n + 1)) :
    stageVectorMatrixEquiv n M ij = M ij.1 ij.2 := by
  rfl

theorem stageVectorMatrixEquiv_symm_apply_pair
    (n : ℕ) (f : StageVector (n + 1)) (ij : TowerMatrix.Idx (n + 1)) :
    (stageVectorMatrixEquiv n).symm f ij.1 ij.2 = f ij := by
  rfl

end InfoGeometry.Canonical
