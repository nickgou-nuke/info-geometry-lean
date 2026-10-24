/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
import InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection

/-! The image of the matrix colimit is exactly the equal-length word core. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge

theorem stageMap_mem_core (n : ℕ) (A : BitWordMatrixStage n) :
    stageMap n A ∈ core := by
  change (∑ i, ∑ j, A i j • complexStarWordPair (List.ofFn i) (List.ofFn j)) ∈ core
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨List.ofFn i, List.ofFn j, by simp, rfl⟩

theorem quotientHom_mem_core (x : Carrier) : quotientHom x ∈ core := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [← stageInjection_apply, quotientHom_stage]
      exact stageMap_mem_core n _

theorem wordPair_mem_range (u v : List Bool) (h : u.length = v.length) :
    complexStarWordPair u v ∈ LinearMap.range quotientAlgHom.toLinearMap := by
  obtain ⟨i, hi⟩ : ∃ i : BitWord u.length, List.ofFn i = u :=
    ⟨u.get, List.ofFn_get u⟩
  obtain ⟨j, hj⟩ : ∃ j : BitWord u.length, List.ofFn j = v := by
    rw [h]
    exact ⟨v.get, List.ofFn_get v⟩
  refine ⟨stageInjection u.length (stageStarAlgEquiv u.length (Matrix.single i j 1)), ?_⟩
  change quotientAlgHom (stageInjection u.length
    (stageStarAlgEquiv u.length (Matrix.single i j 1))) = complexStarWordPair u v
  rw [quotientAlgHom_stage]
  change stageMap u.length ((stageStarAlgEquiv u.length).symm
    (stageStarAlgEquiv u.length (Matrix.single i j 1))) = _
  rw [StarAlgEquiv.symm_apply_apply, stageMap_single, one_smul, hi, hj]

theorem range_quotientAlgHom : LinearMap.range quotientAlgHom.toLinearMap = core := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact quotientHom_mem_core y
  · apply Submodule.span_le.mpr
    rintro x ⟨u, v, h, rfl⟩
    exact wordPair_mem_range u v h

end InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
end
