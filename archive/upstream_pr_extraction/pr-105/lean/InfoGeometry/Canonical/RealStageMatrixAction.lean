import Mathlib
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Matrix actions on finite real Clifford stages

This owner exposes the native `Matrix.mulVecLin` action of a finite stage.
It records the associative action laws without conflating matrix-algebra
embedding with the later, separate Kronecker range theorem.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

def realStageMatrixAction (n : ℕ) (A : MatStage n) :
    (InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ) →ₗ[ℝ]
      (InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ) :=
  A.mulVecLin

@[simp] theorem realStageMatrixAction_apply (n : ℕ)
    (A : MatStage n)
    (x : InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ) :
    realStageMatrixAction n A x = A.mulVec x := rfl

theorem realStageMatrixAction_one (n : ℕ) :
    realStageMatrixAction n (1 : MatStage n) = LinearMap.id := by
  ext x i
  simp [realStageMatrixAction]

theorem realStageMatrixAction_mul (n : ℕ) (A B : MatStage n) :
    realStageMatrixAction n (A * B) =
      (realStageMatrixAction n A).comp (realStageMatrixAction n B) := by
  ext x i
  simp [realStageMatrixAction, Matrix.mulVec_mulVec]

theorem realStageMatrixAction_add (n : ℕ) (A B : MatStage n) :
    realStageMatrixAction n (A + B) =
      realStageMatrixAction n A + realStageMatrixAction n B := by
  ext x i
  simp [realStageMatrixAction]

theorem realStageMatrixAction_smul (n : ℕ) (c : ℝ) (A : MatStage n) :
    realStageMatrixAction n (c • A) =
      c • realStageMatrixAction n A := by
  ext x i
  simp [realStageMatrixAction]

noncomputable def realStageEmbeddedAction (n : ℕ) (A : MatStage n) :
    (InfoGeometry.Clifford.TowerMatrix.Idx (n + 1) → ℝ) →ₗ[ℝ]
      (InfoGeometry.Clifford.TowerMatrix.Idx (n + 1) → ℝ) :=
  realStageMatrixAction (n + 1) (stageEmbed n A)

theorem realStageEmbeddedAction_apply (n : ℕ) (A : MatStage n)
    (x : InfoGeometry.Clifford.TowerMatrix.Idx (n + 1) → ℝ) :
    realStageEmbeddedAction n A x = (stageEmbed n A).mulVec x := rfl

end InfoGeometry.Canonical
