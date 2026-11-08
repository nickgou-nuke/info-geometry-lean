/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Finite tensor factorization of the binary matrix stages

The existing binary operator stage at depth `n + m` factors as the tensor
product of its depth-`n` and depth-`m` stages.  This is an algebra equivalence
of the actual noncommutative matrix carriers used by the `Cl(1,1)` tower.
It does not assert an infinite-factor absorption or a new Clifford-algebra
classification.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorStageFactorization

open scoped Kronecker TensorProduct

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11StarAlgebraColimit
open InfoGeometry.Clifford.TowerMatrix

/-- Split a binary tensor index at the `n`-th position. -/
def idxAddEquiv (n : ℕ) : (m : ℕ) → Idx (n + m) ≃ Idx n × Idx m
  | 0 => by
      letI : Unique (Idx 0) := {
        default := ⟨0, by decide⟩
        uniq := fun x => Subsingleton.elim _ _ }
      exact (Equiv.prodUnique (Idx n) (Idx 0)).symm
  | m + 1 =>
      ((idxAddEquiv n m).prodCongr (Equiv.refl (Fin 2))).trans
        (Equiv.prodAssoc (Idx n) (Idx m) (Fin 2))

/-- The stage at depth `n + m` is the genuine tensor product of the two
matrix stages, via the recursive binary-index split and Mathlib's Kronecker
algebra equivalence. -/
def stageTensorFactorization (n m : ℕ) :
    MatStage (n + m) ≃ₐ[ℝ] TensorProduct ℝ (MatStage n) (MatStage m) :=
  (Matrix.reindexAlgEquiv ℝ ℝ (idxAddEquiv n m)).trans
    (Matrix.kroneckerAlgEquiv (Idx n) (Idx m) ℝ).symm

/-- Under the binary-index reindexing, a Kronecker product of finite-stage
operators is sent to the corresponding elementary tensor. -/
@[simp] theorem stageTensorFactorization_reindex_kronecker
    (n m : ℕ) (A : MatStage n) (B : MatStage m) :
    stageTensorFactorization n m
      (Matrix.reindex (idxAddEquiv n m).symm (idxAddEquiv n m).symm (A ⊗ₖ B)) =
      A ⊗ₜ[ℝ] B := by
  change (Matrix.kroneckerAlgEquiv (Idx n) (Idx m) ℝ).symm
    (Matrix.reindexAlgEquiv ℝ ℝ (idxAddEquiv n m)
      (Matrix.reindex (idxAddEquiv n m).symm (idxAddEquiv n m).symm (A ⊗ₖ B))) = _
  have hreindex :
      Matrix.reindexAlgEquiv ℝ ℝ (idxAddEquiv n m)
        (Matrix.reindex (idxAddEquiv n m).symm (idxAddEquiv n m).symm (A ⊗ₖ B)) =
        A ⊗ₖ B := by
    ext i j
    simp [Matrix.reindex]
  rw [hreindex]
  apply (Matrix.kroneckerAlgEquiv (Idx n) (Idx m) ℝ).injective
  simp

/-- The inverse factorization sends a pure tensor to the reindexed
Kronecker operator. This gives the stage split a normal form in both
directions, which is useful when transporting finite-stage tower maps. -/
@[simp] theorem stageTensorFactorization_symm_tmul
    (n m : ℕ) (A : MatStage n) (B : MatStage m) :
    (stageTensorFactorization n m).symm (A ⊗ₜ[ℝ] B) =
      Matrix.reindex (idxAddEquiv n m).symm (idxAddEquiv n m).symm (A ⊗ₖ B) := by
  apply (stageTensorFactorization n m).injective
  rw [(stageTensorFactorization n m).apply_symm_apply]
  exact (stageTensorFactorization_reindex_kronecker n m A B).symm

/-- The finite-stage binary split is compatible with appending one tensor
factor to its right component. -/
theorem stageTensorFactorization_stageEmbed_tmul
    (n m : ℕ) (A : MatStage n) (B : MatStage m) :
    stageTensorFactorization n (m + 1)
      (stageEmbed (n + m) ((stageTensorFactorization n m).symm (A ⊗ₜ[ℝ] B))) =
        A ⊗ₜ[ℝ] stageEmbed m B := by
  apply (Matrix.kroneckerAlgEquiv (Idx n) (Idx (m + 1)) ℝ).injective
  rw [stageTensorFactorization_symm_tmul]
  simp only [stageTensorFactorization, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply]
  change Matrix.reindex (idxAddEquiv n (m + 1)) (idxAddEquiv n (m + 1))
      (matStageEmbed (n + m)
        (Matrix.reindex (idxAddEquiv n m).symm (idxAddEquiv n m).symm (A ⊗ₖ B))) =
    A ⊗ₖ matStageEmbed m B
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases i₂ with ⟨i₂, i₃⟩
  rcases j with ⟨j₁, j₂⟩
  rcases j₂ with ⟨j₂, j₃⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hidx (a : Idx n) (b : Idx m) (c : Fin 2) :
      (idxAddEquiv n (m + 1)).symm (a, (b, c)) = ((idxAddEquiv n m).symm (a, b), c) := by
    change ((idxAddEquiv n m).prodCongr (Equiv.refl (Fin 2))).symm
      ((Equiv.prodAssoc (Idx n) (Idx m) (Fin 2)).symm (a, (b, c))) = _
    rfl
  rw [hidx i₁ i₂ i₃, hidx j₁ j₂ j₃]
  simp [matStageEmbed, Matrix.submatrix, Matrix.one_apply,
    Matrix.kroneckerMap_apply]
  change (if i₃ = j₃ then A i₁ j₁ * B i₂ j₂ else 0) =
    A i₁ j₁ * (B i₂ j₂ * (if i₃ = j₃ then (1 : ℝ) else 0))
  simp

/-- Naturality of the finite-stage split on the entire tensor-product
carrier: the successor embedding on the combined stage is the identity on the
left factor tensored with the successor embedding on the right factor. -/
theorem stageTensorFactorization_stageEmbed_map
    (n m : ℕ) (z : TensorProduct ℝ (MatStage n) (MatStage m)) :
    stageTensorFactorization n (m + 1)
      (stageEmbed (n + m) ((stageTensorFactorization n m).symm z)) =
    TensorProduct.map (LinearMap.id : MatStage n →ₗ[ℝ] MatStage n)
      (stageEmbed m).toLinearMap z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul A B =>
      simpa using stageTensorFactorization_stageEmbed_tmul n m A B

/-- The factorized finite matrix stage maps canonically into the existing
direct-limit operator algebra. -/
noncomputable def factorizedStageToLimit (n m : ℕ) :
    TensorProduct ℝ (MatStage n) (MatStage m) →ₐ[ℝ] Limit :=
  (ofStageStarAlgHom (n + m)).toAlgHom.comp
    (stageTensorFactorization n m).symm.toAlgHom

/-- The maps from the factorized finite stages into the direct limit are
compatible with advancing the right tensor factor. -/
theorem factorizedStageToLimit_stageEmbed
    (n m : ℕ) (z : TensorProduct ℝ (MatStage n) (MatStage m)) :
    factorizedStageToLimit n (m + 1)
      (TensorProduct.map (LinearMap.id : MatStage n →ₗ[ℝ] MatStage n)
        (stageEmbed m).toLinearMap z) =
      factorizedStageToLimit n m z := by
  change ofStage (n + (m + 1))
      ((stageTensorFactorization n (m + 1)).symm
        (TensorProduct.map (LinearMap.id : MatStage n →ₗ[ℝ] MatStage n)
          (stageEmbed m).toLinearMap z)) =
    ofStage (n + m) ((stageTensorFactorization n m).symm z)
  have hcompat := stageTensorFactorization_stageEmbed_map n m z
  have hstage :
      stageEmbed (n + m) ((stageTensorFactorization n m).symm z) =
        (stageTensorFactorization n (m + 1)).symm
          (TensorProduct.map (LinearMap.id : MatStage n →ₗ[ℝ] MatStage n)
            (stageEmbed m).toLinearMap z) := by
    simpa using congrArg (stageTensorFactorization n (m + 1)).symm hcompat
  rw [← hstage]
  change ofStage ((n + m) + 1)
      (stageEmbed (n + m) ((stageTensorFactorization n m).symm z)) = _
  exact ofStage_apply_bond (n + m) ((stageTensorFactorization n m).symm z)

end InfoGeometry.Clifford.Cl11TensorStageFactorization
