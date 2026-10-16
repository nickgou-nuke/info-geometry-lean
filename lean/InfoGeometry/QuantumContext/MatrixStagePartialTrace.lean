/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
import InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit
import InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Trace-adjoint partial trace for the matrix-stage embeddings

The full matrix successor map is `A ↦ A ⊗ I₂`, reindexed to the standard
dyadic carrier. The partial trace below is its adjoint for the normalized
matrix-trace pairing; all observables and densities remain full matrices.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStagePartialTrace

open scoped Kronecker
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

/-- The unnormalized full-matrix partial trace over a finite second index. -/
theorem trace_mul_partialTraceSecondOp
    {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (D : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) :
    Matrix.trace (A * partialTraceSecondOp D) =
      Matrix.trace ((A ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) * D) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    partialTraceSecondOp, Matrix.kronecker_apply, Fintype.sum_prod_type]
  simp [Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

/-- The normalized partial trace between neighboring dyadic stages. -/
def normalizedPartialTraceStep (n : ℕ)
    (D : MatrixStage (n + 1)) : MatrixStage n :=
  (1 / 2 : ℂ) • partialTraceSecondOp
    ((Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).symm D)

/-- The normalized partial trace is a left inverse of the tower embedding. -/
theorem normalizedPartialTraceStep_concreteStep (n : ℕ)
    (A : MatrixStage n) :
    normalizedPartialTraceStep n (concreteStep n A) = A := by
  ext i j
  simp [normalizedPartialTraceStep, concreteStep, partialTraceSecondOp]

/-- The neighboring-stage normalized trace-adjoint identity. -/
theorem normalizedPartialTraceStep_adjoint (n : ℕ)
    (A : MatrixStage n) (D : MatrixStage (n + 1)) :
    matrixTraceFunctional n (A * normalizedPartialTraceStep n D) =
      matrixTraceFunctional (n + 1) (concreteStep n A * D) := by
  classical
  let e := Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)
  let D' := e.symm D
  have hD : e D' = D := e.apply_symm_apply D
  have htrace := trace_mul_partialTraceSecondOp A D'
  have hstage : Matrix.trace (concreteStep n A * D) =
      Matrix.trace ((A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * D') := by
    change Matrix.trace (e (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * D) = _
    rw [← hD]
    calc
      Matrix.trace (e (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * e D') =
          Matrix.trace (e ((A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * D')) := by
            rw [← map_mul e]
      _ = Matrix.trace ((A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * D') :=
        trace_reindex (stageIndexEquiv n)
          ((A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * D')
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  change (1 / (2 ^ n : ℂ)) *
      Matrix.trace (A * ((1 / 2 : ℂ) • partialTraceSecondOp D')) =
    (1 / (2 ^ (n + 1) : ℂ)) * Matrix.trace (concreteStep n A * D)
  rw [Matrix.mul_smul, Matrix.trace_smul, htrace, hstage]
  have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ n * 2 := by
    rw [pow_succ]
  rw [hpow]
  have hne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp
  ring

/-- A density family is compatible with the normalized trace when each
stage is the normalized partial trace of the next stage. -/
def PartialTraceCompatible (D : ∀ n : ℕ, MatrixStage n) : Prop :=
  ∀ n, D n = normalizedPartialTraceStep n (D (n + 1))

/-- One successor step of the weighted functional is compatible whenever its
density is the normalized partial trace of the next density. -/
theorem weightedStageFunctional_step
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : PartialTraceCompatible D) (n : ℕ) (A : MatrixStage n) :
    weightedStageFunctional D (n + 1) (concreteStep n A) =
      weightedStageFunctional D n A := by
  rw [weightedStageFunctional_apply, weightedStageFunctional_apply, hD n]
  exact (normalizedPartialTraceStep_adjoint n A (D (n + 1))).symm

/-- Backward partial-trace compatibility supplies the `WeightedCompatible`
family needed by the existing categorical colimit functional. -/
theorem weightedStageFunctional_compatible_of_partialTraceCompatible
    (D : ∀ n : ℕ, MatrixStage n) (hD : PartialTraceCompatible D) :
    WeightedCompatible D := by
  intro i j hij x
  induction hij with
  | refl =>
      simp [rawMap,
        InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteMap_id]
  | @step j hij ih =>
      rw [show rawMap (Nat.le.step hij) x =
        concreteStep j (rawMap hij x) by
          simpa [rawMap, concreteData,
            InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteMap,
            InfoGeometry.Canonical.CuntzMatrixTraceTower.map_succ] using
            congrArg (fun f => f x)
              (InfoGeometry.Canonical.CuntzMatrixTraceTower.map_succ
                concreteData hij)]
      exact (weightedStageFunctional_step D hD j (rawMap hij x)).trans ih

/-- A family satisfying the backward partial-trace law descends to the
repository's canonical BitWord matrix-stage quotient colimit. -/
def partialTraceCompatibleColimitFunctional
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : PartialTraceCompatible D) :
    InfoGeometry.Canonical.MatrixStageInductiveLimit.MatrixStageLimit → ℂ :=
  weightedMatrixStageColimitFunctional D
    (weightedStageFunctional_compatible_of_partialTraceCompatible D hD)

/-- Finite-stage readout for the partial-trace-compatible colimit functional. -/
@[simp]
theorem partialTraceCompatibleColimitFunctional_stage
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : PartialTraceCompatible D) (n : ℕ)
    (A : InfoGeometry.Canonical.ComplexMatrixStage.Stage n) :
    partialTraceCompatibleColimitFunctional D hD
      (InfoGeometry.Canonical.MatrixStageInductiveLimit.canonicalStageHom n A) =
        matrixTraceFunctional n
          (InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge.stageStarAlgEquiv n A * D n) := by
  exact InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit.weightedMatrixStageColimitFunctional_stageEquiv D
    (weightedStageFunctional_compatible_of_partialTraceCompatible D hD) n A

end InfoGeometry.QuantumContext.MatrixStagePartialTrace

end
