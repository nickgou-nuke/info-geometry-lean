/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11TensorTower
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

end InfoGeometry.Clifford.Cl11TensorStageFactorization
