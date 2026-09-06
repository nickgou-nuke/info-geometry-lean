import Mathlib.Tactic
import InfoGeometry.Canonical.BitWordComplexStageReindex
import InfoGeometry.Canonical.BoundaryBondSquare
import InfoGeometry.Canonical.CuntzMatrixTraceTower

noncomputable section

namespace InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.BitWordComplexStageReindex
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Algebra.CliffordBitWordEquivalence

/--
The BitWord-indexed complex matrix stage and the standard `Fin (2^n)` complex
matrix stage are star-algebra equivalent.  This packages the already-proved
reindexing equivalence together with its star-compatibility theorem.
-/
noncomputable def stageStarAlgEquiv (n : ℕ) :
    ComplexMatrixStage.Stage n ≃⋆ₐ[ℂ] MatrixStage n :=
  StarAlgEquiv.ofAlgEquiv
    (BitWordComplexStageReindex.equiv n)
    (BitWordComplexStageReindex.equiv_star n)

@[simp] theorem stageStarAlgEquiv_apply
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    stageStarAlgEquiv n A = BitWordComplexStageReindex.equiv n A :=
  rfl

@[simp] theorem stageStarAlgEquiv_map_star
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    stageStarAlgEquiv n (star A) = star (stageStarAlgEquiv n A) := by
  exact map_star (stageStarAlgEquiv n) A

/--
The recursive BitWord block embedding is carried by the canonical stage
reindexing to the standard Kronecker embedding `A ↦ A ⊗ I₂`.

This is the missing naturality square between the two complex dyadic matrix
towers.  No completion and no infinite-algebra identification is used here.
-/
theorem stageStarAlgEquiv_bond
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    stageStarAlgEquiv (n + 1) (ComplexMatrixStage.bondFun n A) =
      concreteStep n (stageStarAlgEquiv n A) := by
  ext i j
  cases hi : (stageIndexEquiv n).symm i with
  | mk i₁ i₂ =>
      cases hj : (stageIndexEquiv n).symm j with
      | mk j₁ j₂ =>
          dsimp [stageStarAlgEquiv, BitWordComplexStageReindex.equiv,
            concreteStep, Matrix.reindexAlgEquiv, Matrix.reindex]
          rw [hi, hj]
          change
            ComplexMatrixStage.bondFun n A
                ((bitWordFinPowTwoEquiv (n + 1)).symm i)
                ((bitWordFinPowTwoEquiv (n + 1)).symm j) =
              A ((bitWordFinPowTwoEquiv n).symm i₁)
                  ((bitWordFinPowTwoEquiv n).symm j₁) *
                (1 : Matrix (Fin 2) (Fin 2) ℂ) i₂ j₂
          simp [ComplexMatrixStage.bondFun, bitWordFinPowTwoEquiv,
            InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordSuccEquiv,
            finTwoEquivBool, Matrix.kronecker_apply,
            hi, hj, extendSucc, prefixSucc, prefixSucc_extendSucc]
          fin_cases i₂ <;> fin_cases j₂ <;>
            simp [extendSucc, prefixSucc, prefixSucc_extendSucc,
              finTwoEquivBool]

/-- The same naturality square expressed with the ring-hom successor bond. -/
theorem stageStarAlgEquiv_bond_hom
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    stageStarAlgEquiv (n + 1) (ComplexMatrixStage.bond n A) =
      concreteStep n (stageStarAlgEquiv n A) := by
  exact stageStarAlgEquiv_bond n A

/--
The canonical normalized trace is invariant under the stage reindexing.
This is the scalar readout needed to transport the compatible trace family
between the BitWord and standard complex matrix towers.
-/
theorem stageStarAlgEquiv_normalizedTrace
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    InfoGeometry.Canonical.GenuineMatrixStageMorphism.normalizedTrace n A =
      matrixTraceState n (stageStarAlgEquiv n A) := by
  simpa [stageStarAlgEquiv_apply] using
    (InfoGeometry.Canonical.BoundaryBondSquare.normalizedTrace_reindex n A)

/--
The normalized trace naturality square is compatible with one successor step.
-/
theorem stageStarAlgEquiv_bond_trace
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    matrixTraceState (n + 1)
        (stageStarAlgEquiv (n + 1) (ComplexMatrixStage.bondFun n A)) =
      matrixTraceState n (stageStarAlgEquiv n A) := by
  rw [stageStarAlgEquiv_bond]
  exact concrete_trace_compatible n (stageStarAlgEquiv n A)

end InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
