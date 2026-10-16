/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticQuadraticDecay
import InfoGeometry.QuantumContext.MarkovChiralBipolarLift

/-!
# Full-matrix decay for the lifted chiral Majorana action

This module specializes the existing weighted-skew quadratic decay theorem to
the actual lifted Jordan--Wigner chiral Majorana operator. The statement is
pointwise on the full matrix carrier and assumes detailed balance and a
nonnegative dissipation rate. It asserts no strict decay or trajectory limit.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin.ChiralBipolarLift

open Matrix
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

variable {k : ℕ}

/-- The lifted chiral Majorana action plus a nonnegative-rate Markov
dissipation has nonpositive instantaneous quadratic pairing on every full
matrix at the Clifford stage `k + 1`. -/
theorem liftedChiralMajorana_quadratic_decay_nonpos
    (scores : Idx (k + 1) → Idx (k + 1) → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (X : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ) :
    weightedMatrixPairing
        (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores) X
        (mulLeftLinearMap (Idx (k + 1)) ℝ
            (weightedSkewActionMatrix
              (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
              (liftedChiralMajorana k)) X -
          γ • markovLeftOnsager
            (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) X) ≤ 0 := by
  have hP : FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores ∈
      Matrix.rowStochastic ℝ (Idx (k + 1)) :=
    FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix_mem_rowStochastic scores
  have hDB : InfoGeometry.Probability.DetailedBalance
      (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
      (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) :=
    FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_detailedBalance
      scores hsymm
  have hπpos : ∀ i, 0 <
      FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores i :=
    FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_pos scores
  exact weightedSkewAction_quadratic_decay_nonpos
    (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
    (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
    hP hDB hπpos (liftedChiralMajorana k) (liftedChiralMajorana_skew k)
    γ hγ X

end InfoGeometry.QuantumContext.MarkovDrazin.ChiralBipolarLift
