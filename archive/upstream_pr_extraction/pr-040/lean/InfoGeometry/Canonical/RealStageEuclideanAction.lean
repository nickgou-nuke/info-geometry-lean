import Mathlib
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.RealStageMatrixAction

/-!
# Euclidean adapter for native finite-stage matrix actions

`TowerMatrix` deliberately exposes its vectors as functions.  This owner keeps
that carrier unchanged and supplies the standard real `EuclideanSpace` view
needed by Mathlib's inner-product and isometry APIs.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

abbrev StageEuclideanVector (n : ℕ) :=
  EuclideanSpace ℝ (TowerMatrix.Idx n)

noncomputable def stageVectorEquiv (n : ℕ) :
    (TowerMatrix.Idx n → ℝ) ≃ₗ[ℝ] StageEuclideanVector n where
  toFun := WithLp.toLp 2
  invFun := WithLp.ofLp
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def stageEuclideanAction (n : ℕ) (A : MatStage n) :
    StageEuclideanVector n →ₗ[ℝ] StageEuclideanVector n :=
  (stageVectorEquiv n).toLinearMap.comp
    ((realStageMatrixAction n A).comp (stageVectorEquiv n).symm.toLinearMap)

@[simp] theorem stageEuclideanAction_apply (n : ℕ) (A : MatStage n)
    (x : StageEuclideanVector n) :
    stageEuclideanAction n A x =
      stageVectorEquiv n (realStageMatrixAction n A ((stageVectorEquiv n).symm x)) :=
  rfl

theorem stageEuclideanAction_one (n : ℕ) :
    stageEuclideanAction n (1 : MatStage n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [stageEuclideanAction, realStageMatrixAction_one]

theorem stageEuclideanAction_mul (n : ℕ) (A B : MatStage n) :
    stageEuclideanAction n (A * B) =
      (stageEuclideanAction n A).comp (stageEuclideanAction n B) := by
  simp only [stageEuclideanAction, realStageMatrixAction_mul]
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
  congr 1

theorem euclideanMatrixAction_transpose_inner
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (WithLp.toLp 2 (Matrix.mulVec A.transpose x.ofLp)) y =
      inner ℝ x (WithLp.toLp 2 (Matrix.mulVec A y.ofLp)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.mulVec, dotProduct]
  have hstar (i : ι) :
      star (A.transpose.mulVec x.ofLp i) =
        ∑ j, A j i * x.ofLp j := by
    rw [Matrix.mulVec, dotProduct]
    simp only [Matrix.transpose_apply]
    rw [star_sum]
    simp only [star_trivial]
  simp_rw [Pi.star_apply, hstar]
  simp only [star_trivial]
  calc
    (∑ i, y.ofLp i * ∑ j, A j i * x.ofLp j) =
        ∑ i, ∑ j, y.ofLp i * (A j i * x.ofLp j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, y.ofLp i * (A j i * x.ofLp j) := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, (A j i * y.ofLp i) * x.ofLp j := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ j, (∑ i, A j i * y.ofLp i) * x.ofLp j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]

theorem stageEuclideanAction_star_inner
    (n : ℕ) (A : MatStage n)
    (x y : StageEuclideanVector n) :
    inner ℝ (stageEuclideanAction n (star A) x) y =
      inner ℝ x (stageEuclideanAction n A y) := by
  change inner ℝ
      (WithLp.toLp 2 (Matrix.mulVec (star A)
        x.ofLp)) y =
    inner ℝ x
      (WithLp.toLp 2 (Matrix.mulVec A
        y.ofLp))
  exact euclideanMatrixAction_transpose_inner A x y

theorem stageEuclideanAction_adjoint (n : ℕ) (A : MatStage n) :
    LinearMap.adjoint (stageEuclideanAction n A) =
      stageEuclideanAction n (star A) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.adjoint_inner_left]
  exact (stageEuclideanAction_star_inner n A x y).symm

noncomputable def stageMatrixOfEuclideanMap (n : ℕ)
    (T : StageEuclideanVector n →ₗ[ℝ] StageEuclideanVector n) : MatStage n :=
  (Matrix.toLin').symm
    ((stageVectorEquiv n).symm.toLinearMap.comp
      (T.comp (stageVectorEquiv n).toLinearMap))

theorem stageEuclideanAction_matrixOfEuclideanMap (n : ℕ)
    (T : StageEuclideanVector n →ₗ[ℝ] StageEuclideanVector n) :
    stageEuclideanAction n (stageMatrixOfEuclideanMap n T) = T := by
  apply LinearMap.ext
  intro x
  apply (stageVectorEquiv n).symm.injective
  change realStageMatrixAction n (stageMatrixOfEuclideanMap n T)
      ((stageVectorEquiv n).symm x) =
    (stageVectorEquiv n).symm (T x)
  change (Matrix.toLin' (stageMatrixOfEuclideanMap n T))
      ((stageVectorEquiv n).symm x) = _
  change (Matrix.toLin' ((Matrix.toLin').symm
      ((stageVectorEquiv n).symm.toLinearMap.comp
        (T.comp (stageVectorEquiv n).toLinearMap))))
      ((stageVectorEquiv n).symm x) = _
  rw [(Matrix.toLin').apply_symm_apply]
  simp only [LinearMap.comp_apply]
  change (stageVectorEquiv n).symm
      (T ((stageVectorEquiv n) ((stageVectorEquiv n).symm x))) =
    (stageVectorEquiv n).symm (T x)
  rw [(stageVectorEquiv n).apply_symm_apply x]

theorem stageMatrixOfEuclideanAction (n : ℕ) (A : MatStage n) :
    stageMatrixOfEuclideanMap n (stageEuclideanAction n A) = A := by
  apply (Matrix.toLin').injective
  unfold stageMatrixOfEuclideanMap
  change Matrix.toLin' ((Matrix.toLin').symm
      ((stageVectorEquiv n).symm.toLinearMap.comp
        ((stageEuclideanAction n A).comp
          (stageVectorEquiv n).toLinearMap))) =
    Matrix.toLin' A
  rw [(Matrix.toLin').apply_symm_apply]
  apply LinearMap.ext
  intro x
  change (stageVectorEquiv n).symm
      (stageEuclideanAction n A ((stageVectorEquiv n) x)) =
    A.mulVec x
  simp [stageEuclideanAction, realStageMatrixAction]

theorem stageEuclideanAction_injective (n : ℕ) :
    Function.Injective (stageEuclideanAction n) := by
  intro A B h
  calc
    A = stageMatrixOfEuclideanMap n (stageEuclideanAction n A) :=
      (stageMatrixOfEuclideanAction n A).symm
    _ = stageMatrixOfEuclideanMap n (stageEuclideanAction n B) :=
      congrArg (stageMatrixOfEuclideanMap n) h
    _ = B := stageMatrixOfEuclideanAction n B

end
end InfoGeometry.Canonical
