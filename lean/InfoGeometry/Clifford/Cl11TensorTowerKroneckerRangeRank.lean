import InfoGeometry.Canonical.RealStageKroneckerAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealProjectionRankConjugation
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Range rank of the native `A ↦ A ⊗ I₂` embedding

The rank here is the finite-dimensional rank of the associated matrix action,
expressed as the finrank of its linear-map range.  The proof factors through
the existing two-copy vector equivalence and the native product-range
equivalence; no `Matrix.rank` or determinant calculation is used.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower

def stageLinearMap (n : ℕ) (A : MatStage n) :
    (TowerMatrix.Idx n → ℝ) →ₗ[ℝ] (TowerMatrix.Idx n → ℝ) :=
  realStageMatrixAction n A

theorem conjugate_stageEmbeddedAction
    (n : ℕ) (A : MatStage n) :
    conjugateLinearMap (realStageVectorDouble n)
      (stageLinearMap (n + 1) (matStageEmbed n A)) =
      doubleProjection (stageLinearMap n A) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext i
    change (∑ j : TowerMatrix.Idx n × Fin 2,
      (matStageEmbed n A) (i, (0 : Fin 2)) j *
        (match j.2 with
        | 0 => x.1 j.1
        | 1 => x.2 j.1)) =
      ∑ j, A i j * x.1 j
    simp [Fintype.sum_prod_type, matStageEmbed,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
  · funext i
    change (∑ j : TowerMatrix.Idx n × Fin 2,
      (matStageEmbed n A) (i, (1 : Fin 2)) j *
        (match j.2 with
        | 0 => x.1 j.1
        | 1 => x.2 j.1)) =
      ∑ j, A i j * x.2 j
    simp [Fintype.sum_prod_type, matStageEmbed,
      Matrix.kroneckerMap_apply, Matrix.one_apply]

noncomputable def stageRangeEquiv
    (n : ℕ) (A : MatStage n) :
    LinearMap.range (stageLinearMap (n + 1) (matStageEmbed n A)) ≃ₗ[ℝ]
      (LinearMap.range (stageLinearMap n A) ×
        LinearMap.range (stageLinearMap n A)) := by
  let e₁ := conjugateRangeEquiv (realStageVectorDouble n)
    (stageLinearMap (n + 1) (matStageEmbed n A))
  have h₁ : LinearMap.range (conjugateLinearMap (realStageVectorDouble n)
      (stageLinearMap (n + 1) (matStageEmbed n A))) =
      LinearMap.range (doubleProjection (stageLinearMap n A)) :=
    congrArg LinearMap.range (conjugate_stageEmbeddedAction n A)
  let e₁' : LinearMap.range (conjugateLinearMap (realStageVectorDouble n)
      (stageLinearMap (n + 1) (matStageEmbed n A))) ≃ₗ[ℝ]
      LinearMap.range (doubleProjection (stageLinearMap n A)) :=
    LinearEquiv.ofEq
      (LinearMap.range (conjugateLinearMap (realStageVectorDouble n)
        (stageLinearMap (n + 1) (matStageEmbed n A))))
      (LinearMap.range (doubleProjection (stageLinearMap n A))) h₁
  let e₂ := doubleProjectionRangeEquiv (stageLinearMap n A)
  exact e₁.trans (e₁'.trans e₂)

noncomputable def range_stageEmbed_equiv_prod
    (n : ℕ) (A : MatStage n) :
    LinearMap.range (stageLinearMap (n + 1) (matStageEmbed n A)) ≃ₗ[ℝ]
      (LinearMap.range (stageLinearMap n A) ×
        LinearMap.range (stageLinearMap n A)) :=
  stageRangeEquiv n A

noncomputable def stageRank (n : ℕ) (A : MatStage n) : ℕ :=
  Module.finrank ℝ (LinearMap.range (stageLinearMap n A))

theorem stageRank_embed (n : ℕ) (A : MatStage n) :
    stageRank (n + 1) (matStageEmbed n A) = 2 * stageRank n A := by
  unfold stageRank
  rw [(stageRangeEquiv n A).finrank_eq]
  rw [Module.finrank_prod]
  rw [two_mul]

noncomputable def normalizedStageRank (n : ℕ) (A : MatStage n) : ℚ :=
  (stageRank n A : ℚ) / (2 : ℚ) ^ n

@[simp] theorem normalizedStageRank_embed (n : ℕ) (A : MatStage n) :
    normalizedStageRank (n + 1) (matStageEmbed n A) =
      normalizedStageRank n A := by
  unfold normalizedStageRank
  rw [stageRank_embed, pow_succ]
  field_simp
  norm_num [Nat.cast_mul]

end InfoGeometry.Canonical
