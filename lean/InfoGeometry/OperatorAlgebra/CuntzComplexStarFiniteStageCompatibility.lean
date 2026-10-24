/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom
import InfoGeometry.Canonical.GenuineMatrixStageMorphism

/-! Compatibility with the coherent right-extension matrix bond. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge

theorem stageHom_bond (n : ℕ) (A : BitWordMatrixStage n) :
    stageHom (n + 1) (InfoGeometry.Canonical.ComplexMatrixStage.bondFun n A) =
      stageHom n A := by
  change stageMap (n + 1) (InfoGeometry.Canonical.ComplexMatrixStage.bondFun n A) =
    stageMap n A
  rw [bondFun_eq_dyadicMatrixEmbedding]
  unfold dyadicMatrixEmbedding
  simp only [map_sum, map_smul, map_add, stageMap_single, one_smul]
  change _ = ∑ u : BitWord n, ∑ v : BitWord n,
    A u v • complexStarWordPair (List.ofFn u) (List.ofFn v)
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp_rw [list_ofFn_extendBitWord]
  congr 1
  simpa only [Fintype.sum_bool, add_comm] using
    wordPair_refinement (List.ofFn u) (List.ofFn v)

end InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom
end
