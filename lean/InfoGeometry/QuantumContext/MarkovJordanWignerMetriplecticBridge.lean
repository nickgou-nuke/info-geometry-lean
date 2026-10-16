/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.QuantumContext.MarkovMetriplecticReversibleRotation

/-!
# Jordan--Wigner Majorana input to the Markov metriplectic bridge

The reversible/dissipative bridge accepts a skew operator as data. This file
supplies a nonzero real Clifford matrix from the repository's Jordan--Wigner
CAR owner, and transports that skew seed to the stationary-weighted pairing
using the existing weighted action construction. The group inverse continues
to invert only the Markov Laplacian range; it is not identified with the
Clifford generator.

The full matrix carrier is retained throughout. The Markov transition is a
symmetric-score softmax, while the Clifford seed acts by left multiplication
on the full matrix algebra. No diagonal restriction is used.
-/

open scoped TensorProduct DirectSum Matrix Kronecker

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

instance idxSuccNontrivial (k : ℕ) : Nontrivial (Idx (k + 1)) := by
  dsimp [Idx]
  infer_instance

/-- The real matrix Majorana direction obtained from the CAR creation and
annihilation generators at one newly appended Clifford site. -/
def majoranaDifference (k : ℕ) : MatStage (k + 1) :=
  jw_u_new k - jw_v_new k

theorem gammaChiralBase_transpose : gamma_chiral_baseᵀ = gamma_chiral_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem globalChirality_transpose (k : ℕ) :
    (globalChirality k)ᵀ = globalChirality k := by
  exact Jn_transpose gamma_chiral_base gammaChiralBase_transpose k

theorem aDaggerBase_transpose : a_dagger_baseᵀ = a_base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem aBase_transpose : a_baseᵀ = a_dagger_base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Transposition exchanges the repository's real Jordan--Wigner creation
and annihilation matrices. -/
theorem jw_u_new_transpose (k : ℕ) : (jw_u_new k)ᵀ = jw_v_new k := by
  change ((globalChirality k) ⊗ₖ a_dagger_base)ᵀ =
    (globalChirality k) ⊗ₖ a_base
  rw [transpose_kronecker, globalChirality_transpose, aDaggerBase_transpose]

theorem jw_v_new_transpose (k : ℕ) : (jw_v_new k)ᵀ = jw_u_new k := by
  change ((globalChirality k) ⊗ₖ a_base)ᵀ =
    (globalChirality k) ⊗ₖ a_dagger_base
  rw [transpose_kronecker, globalChirality_transpose, aBase_transpose]

/-- The Jordan--Wigner Majorana difference is skew under matrix transpose. -/
theorem majoranaDifference_skew (k : ℕ) :
    (majoranaDifference k)ᵀ = -majoranaDifference k := by
  simp only [majoranaDifference, Matrix.transpose_sub,
    jw_u_new_transpose, jw_v_new_transpose]
  abel

/-- The real Jordan--Wigner Majorana direction squares to `-1`, by the CAR
relations at its site. -/
theorem majoranaDifference_sq (k : ℕ) :
    majoranaDifference k * majoranaDifference k = -1 := by
  unfold majoranaDifference
  calc
    (jw_u_new k - jw_v_new k) * (jw_u_new k - jw_v_new k) =
        jw_u_new k * jw_u_new k - jw_u_new k * jw_v_new k -
          jw_v_new k * jw_u_new k + jw_v_new k * jw_v_new k := by
          noncomm_ring
    _ = -(jw_u_new k * jw_v_new k + jw_v_new k * jw_u_new k) := by
      rw [jw_u_new_sq, jw_v_new_sq]
      noncomm_ring
    _ = -1 := by rw [jw_uv_anticomm_new]

/-- In particular the Clifford seed is a genuine nonzero operator. -/
theorem majoranaDifference_ne_zero (k : ℕ) : majoranaDifference k ≠ 0 := by
  intro h
  have hsq := congrArg (fun X : MatStage (k + 1) => X * X) h
  rw [majoranaDifference_sq] at hsq
  norm_num at hsq

/-- The real Clifford matrix acts on the full matrix algebra by left
multiplication; the weighted skew construction keeps the stationary pairing
valid when softmax partition weights are nonuniform. -/
def weightedMajoranaAction (k : ℕ) (π : Idx (k + 1) → ℝ) :
    Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ →ₗ[ℝ]
      Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ :=
  mulLeftLinearMap (Idx (k + 1)) ℝ
    (weightedSkewActionMatrix π (majoranaDifference k))

/-- A concrete Jordan--Wigner reversible action has zero instantaneous
energy pairing when combined with the symmetric-softmax Markov dissipation.
The reversible input is the weighted transform of a genuine Clifford
Majorana matrix, not the unweighted matrix when stationary weights vary. -/
theorem symmetricSoftmax_majorana_energy_balance
    (k : ℕ) (scores : Idx (k + 1) → Idx (k + 1) → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (entropyForce : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ) :
    weightedMatrixPairing
        (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
        (constantOneMatrix (ι := Idx (k + 1)))
      (weightedMajoranaAction k
          (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
          (constantOneMatrix (ι := Idx (k + 1))) +
        markovLeftOnsager
          (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
          entropyForce) = 0 := by
  unfold weightedMajoranaAction
  exact symmetricSoftmax_weightedSkewAction_energy_balance scores hsymm
    entropyForce (majoranaDifference k) (majoranaDifference_skew k)

/-- Joint Green-operator and Clifford/Majorana bridge. For symmetric-score
softmax, the Markov group inverse recovers the projected dissipative force,
while the actual Jordan--Wigner Majorana seed supplies a nonzero reversible
action with zero instantaneous pairing against the constant energy force.
The carrier is the full noncommutative matrix algebra at Clifford stage
`k + 1`. -/
theorem exists_symmetricSoftmax_groupInverse_majorana_balance
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
      majoranaDifference k ≠ 0 ∧
      ∃ X Y : Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ, X * Y ≠ Y * X := by
  obtain ⟨G, hG, hRecover, hBalance⟩ :=
    exists_symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance
      scores hsymm entropyForce (majoranaDifference k) (majoranaDifference_skew k)
  exact ⟨G, hG, hRecover, hBalance, majoranaDifference_ne_zero k,
    matrix_noncommutative_witness⟩

end InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner
