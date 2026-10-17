/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.QuantumContext.MatrixGNS
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.AttentionStageColimitState

/-!
# Finite matrix GNS adjoint for congruence maps

For a rectangular matrix `C`, the map `A ↦ Cᵀ A C` sends full matrices on one
finite carrier to full matrices on another. This file computes its adjoint for
the weighted GNS pairings `Tr (ρ Aᵀ B)`. The formula is a density-weighted
transpose. The result is an adjoint identity; it does not assert that the
congruence is unital, trace-preserving, completely positive, or the standard
state-dependent Petz recovery map.

The final theorem instantiates the identity with the strictly positive finite
softmax attention density. No colimit-wide map is asserted because the existing
selected-stage attention states have no general inter-stage coarse-graining
compatibility theorem.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionGNSWeightedAdjoint

open Matrix
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The rectangular congruence map from full matrices on `ι` to full
matrices on `κ`. No channel or normalization property is implicit. -/
def congruenceMap (C : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  Cᵀ * A * C

/-- The density-weighted transpose associated with the two bilinear trace
pairings. -/
def weightedTransposeForPairing (C : Matrix ι κ ℝ) (rhoInv : Matrix ι ι ℝ)
    (sigma B : Matrix κ κ ℝ) : Matrix ι ι ℝ :=
  C * B * sigma * Cᵀ * rhoInv

/-- Exact adjoint identity for rectangular congruence with respect to the
bilinear trace pairings `Tr (rho Aᵀ B)` and `Tr (sigma Aᵀ B)`. The attention
specialization below has positive density matrices, hence genuine GNS inner
products. In this generic statement no positivity claim is made. -/
theorem weightedPairing_congruenceMap_adjointIdentity
    (C : Matrix ι κ ℝ) (rho rhoInv : Matrix ι ι ℝ)
    (sigma : Matrix κ κ ℝ) (hρ : rhoInv * rho = 1)
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    MatrixGNS.gnsInner sigma (congruenceMap C A) B =
      MatrixGNS.gnsInner rho A (weightedTransposeForPairing C rhoInv sigma B) := by
  unfold MatrixGNS.gnsInner congruenceMap weightedTransposeForPairing
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hcycle : Matrix.trace (sigma * Cᵀ * Aᵀ * C * B) =
      Matrix.trace (Aᵀ * C * B * sigma * Cᵀ) := by
    calc
      Matrix.trace (sigma * Cᵀ * Aᵀ * C * B) =
          Matrix.trace ((sigma * Cᵀ * Aᵀ * C) * B) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (B * (sigma * Cᵀ * Aᵀ * C)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((B * sigma * Cᵀ) * (Aᵀ * C)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Aᵀ * C) * (B * sigma * Cᵀ)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Aᵀ * C * B * sigma * Cᵀ) := by
            simp only [Matrix.mul_assoc]
  have hcancel : Matrix.trace (rho * Aᵀ * C * B * sigma * Cᵀ * rhoInv) =
      Matrix.trace (Aᵀ * C * B * sigma * Cᵀ) := by
    calc
      Matrix.trace (rho * Aᵀ * C * B * sigma * Cᵀ * rhoInv) =
          Matrix.trace (rhoInv * (rho * Aᵀ * C * B * sigma * Cᵀ)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Aᵀ * C * B * sigma * Cᵀ) := by
            simp only [← Matrix.mul_assoc]
            rw [hρ, Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using hcycle.trans hcancel.symm

/-- Attention specialization: the GNS adjoint of a finite-stage matrix
congruence is its Boltzmann-weighted transpose with respect to the softmax
density. -/
theorem attentionGns_congruence_adjoint
    [Nonempty ι] (logits : ι → ℝ) (β : ℝ)
    (C A B : Matrix ι ι ℝ) :
    MatrixGNS.gnsInner (AttentionKMSState.attentionDensityMatrix logits β)
        (congruenceMap C A) B =
      MatrixGNS.gnsInner (AttentionKMSState.attentionDensityMatrix logits β) A
        (weightedTransposeForPairing C
          (AttentionKMSState.attentionDensityMatrixInv logits β)
          (AttentionKMSState.attentionDensityMatrix logits β) B) := by
  exact weightedPairing_congruenceMap_adjointIdentity C
    (AttentionKMSState.attentionDensityMatrix logits β)
    (AttentionKMSState.attentionDensityMatrixInv logits β)
    (AttentionKMSState.attentionDensityMatrix logits β)
    (AttentionKMSState.attentionDensityMatrixInv_mul logits β) A B

/-- The finite-stage GNS adjoint identity is read identically by the
repository's selected-stage attention functional on the noncommutative matrix
colimit. The statement is stage-local: it does not assert compatibility for
independently chosen logits or congruence maps at different stages. -/
theorem attentionSelectedColimit_congruence_adjoint (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (C A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k
        (AttentionStageColimitState.attentionStageDensity k logits β)
        (InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection k
          (AttentionStageColimitState.complexifyRealMatrix
            ((congruenceMap C A)ᵀ * B))) =
      selectedStageColimitFunctional k
        (AttentionStageColimitState.attentionStageDensity k logits β)
        (InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection k
          (AttentionStageColimitState.complexifyRealMatrix
            (Aᵀ * weightedTransposeForPairing C
              (AttentionKMSState.attentionDensityMatrixInv logits β)
              (AttentionKMSState.attentionDensityMatrix logits β) B))) := by
  have hGNS := attentionGns_congruence_adjoint logits β C A B
  have hState :
      AttentionKMSState.attentionState logits β ((congruenceMap C A)ᵀ * B) =
        AttentionKMSState.attentionState logits β
          (Aᵀ * weightedTransposeForPairing C
            (AttentionKMSState.attentionDensityMatrixInv logits β)
            (AttentionKMSState.attentionDensityMatrix logits β) B) := by
    simpa [AttentionKMSState.attentionState, MatrixGNS.gnsInner,
      Matrix.mul_assoc] using hGNS
  rw [AttentionStageColimitState.attentionColimitFunctional_real_seed_readout,
    AttentionStageColimitState.attentionColimitFunctional_real_seed_readout]
  exact congrArg (algebraMap ℝ ℂ) hState

end InfoGeometry.QuantumContext.AttentionGNSWeightedAdjoint
