/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStagePartialTrace

/-! Product densities compatible with the normalized dyadic matrix trace. -/
noncomputable section
namespace InfoGeometry.QuantumContext.MatrixStageProductDensity

open scoped Kronecker
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.QuantumContext.MatrixStagePartialTrace
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

def density (q : Fin 2 → ℂ) : ∀ n, MatrixStage n
  | 0 => 1
  | n + 1 => Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)
      (density q n ⊗ₖ Matrix.diagonal (fun i => 2 * q i))

theorem partialTrace_tensor_density (q : Fin 2 → ℂ)
    (hq : q 0 + q 1 = 1) (n : ℕ) (D : MatrixStage n) :
    normalizedPartialTraceStep n
      (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)
        (D ⊗ₖ Matrix.diagonal (fun i => 2 * q i))) = D := by
  ext i j
  simp [normalizedPartialTraceStep, partialTraceSecondOp, Fin.sum_univ_two]
  calc
    (2 : ℂ)⁻¹ * (D i j * (2 * q 0) + D i j * (2 * q 1)) =
      D i j * (q 0 + q 1) := by ring
    _ = D i j := by rw [hq, mul_one]

theorem density_compatible (q : Fin 2 → ℂ) (hq : q 0 + q 1 = 1) :
    PartialTraceCompatible (density q) := by
  intro n
  exact (partialTrace_tensor_density q hq n (density q n)).symm

theorem density_trace_one (q : Fin 2 → ℂ) (hq : q 0 + q 1 = 1) (n : ℕ) :
    matrixTraceFunctional n (density q n) = 1 := by
  induction n with
  | zero => simp [density, matrixTraceFunctional_apply, Matrix.trace_one]
  | succ n ih =>
      have h := normalizedPartialTraceStep_adjoint n (1 : MatrixStage n)
        (density q (n + 1))
      rw [← density_compatible q hq n, one_mul, map_one, one_mul] at h
      exact h.symm.trans ih

end InfoGeometry.QuantumContext.MatrixStageProductDensity
end
