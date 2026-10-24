/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits
import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness

/-! The existing finite-stage element map is an injective star-algebra map
into the corrected quotient. Multiplication is proved in that quotient;
finite boundary faithfulness is used only for injectivity.
-/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness

def stageMap (n : ℕ) : BitWordMatrixStage n →ₗ[ℂ] ComplexStarCuntzAlg Bool where
  toFun := complexStarFiniteStageElement n
  map_add' A B := by
    simp [complexStarFiniteStageElement, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [complexStarFiniteStageElement, Finset.smul_sum, smul_smul]

theorem stageMap_single (n : ℕ) (i j : BitWord n) (c : ℂ) :
    stageMap n (Matrix.single i j c) =
      c • complexStarWordPair (List.ofFn i) (List.ofFn j) := by
  have h : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
    ext a b
    simp [Matrix.single]
  rw [h, map_smul]
  exact congrArg (c • ·) (complexStarFiniteStageElement_matrixUnit n i j)

theorem stageMap_one (n : ℕ) : stageMap n 1 = 1 := by
  change (∑ i : BitWord n, ∑ j : BitWord n,
    (1 : BitWordMatrixStage n) i j • complexStarWordPair (List.ofFn i) (List.ofFn j)) = 1
  simpa [Matrix.one_apply] using wordPair_level_sum n

theorem stageMap_mul (n : ℕ) (A B : BitWordMatrixStage n) :
    stageMap n (A * B) = stageMap n A * stageMap n B := by
  classical
  have hsingle (i j k l : BitWord n) (a b : ℂ) :
      stageMap n (Matrix.single i j a * Matrix.single k l b) =
        (a • complexStarWordPair (List.ofFn i) (List.ofFn j)) *
        (b • complexStarWordPair (List.ofFn k) (List.ofFn l)) := by
    rw [smul_mul_smul, wordPair_mul_equal_length _ _ _ _ (by simp)]
    by_cases h : j = k
    · subst k
      simp [Matrix.single_mul_single_same, stageMap_single]
    · have hl : List.ofFn j ≠ List.ofFn k := by simpa using h
      simp [Matrix.single_mul_single_of_ne (c := a) (i := i) (j := j)
        (k := k) (h := h) (d := b), hl]
  rw [Matrix.matrix_eq_sum_single A, Matrix.matrix_eq_sum_single B]
  simp only [map_sum, stageMap_single]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  exact hsingle i j k l _ _

theorem stageMap_star (n : ℕ) (A : BitWordMatrixStage n) :
    stageMap n (star A) = star (stageMap n A) := by
  change (∑ i, ∑ j, star (A j i) • complexStarWordPair (List.ofFn i) (List.ofFn j)) =
    star (∑ i, ∑ j, A i j • complexStarWordPair (List.ofFn i) (List.ofFn j))
  simp only [star_sum, star_complex_smul, wordPair_star]
  rw [Finset.sum_comm]

def stageHom (n : ℕ) : BitWordMatrixStage n →⋆ₐ[ℂ] ComplexStarCuntzAlg Bool where
  toFun := stageMap n
  map_one' := stageMap_one n
  map_mul' := stageMap_mul n
  map_zero' := (stageMap n).map_zero
  map_add' := (stageMap n).map_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, stageMap_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := stageMap_star n

theorem stageHom_injective (n : ℕ) : Function.Injective (stageHom n) := by
  intro A B h
  apply bitWordMatrixLinearRepresentation_injective n
  have hh := congrArg cantorBernoulliComplexStarLift h
  change cantorBernoulliComplexStarLift (complexStarFiniteStageElement n A) =
    cantorBernoulliComplexStarLift (complexStarFiniteStageElement n B) at hh
  rw [complexStarFiniteStageElement_representation,
    complexStarFiniteStageElement_representation] at hh
  exact hh

end InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom
end
