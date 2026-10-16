/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovJordanWignerMetriplecticBridge

/-!
# Nonvanishing of the weighted Jordan--Wigner action

The Markov/Jordan--Wigner balance theorem uses the row-weighted left action
`weightedMajoranaAction`, not just its unweighted Majorana matrix. Strictly
positive weights make rowwise rescaling injective, and evaluation of a left
action at the identity detects its multiplier. The resulting witnesses remain
on the full matrix algebra of the finite Clifford tensor stage.
-/

open scoped TensorProduct DirectSum Matrix Kronecker

namespace InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

/-- Rowwise division by a pointwise nonzero weight cannot send a nonzero
matrix to zero. -/
theorem weightedSkewActionMatrix_ne_zero_of_ne_zero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (S : Matrix ι ι ℝ)
    (hπ : ∀ i, π i ≠ 0) (hS : S ≠ 0) :
    weightedSkewActionMatrix π S ≠ 0 := by
  intro h
  have hS0 : S = 0 := by
    ext i j
    have hentry : weightedSkewActionMatrix π S i j = 0 := by
      simpa using congrFun (congrFun h i) j
    unfold weightedSkewActionMatrix at hentry
    rcases (div_eq_zero_iff).mp hentry with hSij | hπi
    · simpa using hSij
    · exact False.elim (hπ i hπi)
  exact hS hS0

/-- A left-multiplication endomorphism of the full matrix module is detected
by its value at the identity matrix. -/
theorem mulLeftLinearMap_ne_zero_of_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A ≠ 0) :
    mulLeftLinearMap ι ℝ A ≠ 0 := by
  intro h
  apply hA
  have hEval := congrArg (fun T : Matrix ι ι ℝ →ₗ[ℝ]
      Matrix ι ι ℝ => T (1 : Matrix ι ι ℝ)) h
  simpa [mulLeftLinearMap] using hEval

/-- The weighted Majorana action is a nonzero endomorphism whenever all
stationary weights are positive. -/
theorem weightedMajoranaAction_ne_zero_of_positive
    (k : ℕ) (π : Idx (k + 1) → ℝ)
    (hπ : ∀ i, 0 < π i) :
    weightedMajoranaAction k π ≠ 0 := by
  apply mulLeftLinearMap_ne_zero_of_ne_zero
  apply weightedSkewActionMatrix_ne_zero_of_ne_zero
    π (majoranaDifference k) (fun i => (hπ i).ne')
  exact majoranaDifference_ne_zero k

/-- Finite-softmax stationary weights are strictly positive, so the actual
weighted Jordan--Wigner left action in the symmetric-softmax balance is
nonzero on the full matrix module. No score symmetry is needed for this
nonvanishing statement. -/
theorem softmaxWeightedMajoranaAction_ne_zero
    (k : ℕ) (scores : Idx (k + 1) → Idx (k + 1) → ℝ) :
    weightedMajoranaAction k
      (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores) ≠ 0 := by
  apply weightedMajoranaAction_ne_zero_of_positive k
  exact FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_pos scores

/-- Strengthened Jordan--Wigner/Markov balance certificate: in addition to
the group-inverse recovery and zero weighted energy pairing, the actual
reversible endomorphism used by that balance is witnessed nonzero. -/
theorem exists_symmetricSoftmax_groupInverse_majorana_balance_with_nonzero_action
    (k : ℕ) (scores : Idx (k + 1) → Idx (k + 1) → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (entropyForce : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ) :
    ∃ G : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ,
      InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
        (1 - FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G ∧
      G * markovLeftOnsager
          (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) entropyForce =
        markovRangeIdempotent
          (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G * entropyForce ∧
      weightedMatrixPairing
          (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
          (constantOneMatrix (ι := Idx (k + 1)))
        (weightedMajoranaAction k
            (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
            (constantOneMatrix (ι := Idx (k + 1))) +
          markovLeftOnsager
            (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
            entropyForce) = 0 ∧
      weightedMajoranaAction k
        (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores) ≠ 0 := by
  obtain ⟨G, hG, hRecover, hBalance, _hMajorana, _hNoncomm⟩ :=
    exists_symmetricSoftmax_groupInverse_majorana_balance
      k scores hsymm entropyForce
  exact ⟨G, hG, hRecover, hBalance,
    softmaxWeightedMajoranaAction_ne_zero k scores⟩

end InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner
