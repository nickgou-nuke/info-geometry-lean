/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.ChiralBipolarAttention
import InfoGeometry.QuantumContext.MarkovJordanWignerMetriplecticBridge

/-!
# Chiral bipolar routing in the finite Markov–Clifford matrix carrier

The two-dimensional chiral bipolar operator is used only as the local factor
of the repository's existing Jordan–Wigner tensor-stage representation. The
resulting operator acts on the full matrix carrier `MatStage (k + 1)`. The
group inverse remains the range inverse of the symmetric-softmax Markov
Laplacian; no identification of the chiral generator with that inverse is
made.
-/

open scoped TensorProduct DirectSum Matrix Kronecker

namespace InfoGeometry.QuantumContext.MarkovDrazin.ChiralBipolarLift

open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.QuantumContext.ChiralBipolarAttention
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

/-- The base odd chiral channel obtained from the creation-minus-annihilation
matrix. -/
def baseChiralMajorana : Mat2R := a_dagger_base - a_base

/-- The off-diagonal chiral-bipolar projection fixes the odd base generator. -/
theorem chiralBipolar_baseMajorana_eq :
    chiralBipolar baseChiralMajorana = baseChiralMajorana := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseChiralMajorana, chiralBipolar, a_dagger_base, a_base]

/-- Lift the local chiral bipolar generator to the full Clifford tensor-stage
operator carrier by the existing Jordan–Wigner parity string. -/
noncomputable def liftedChiralMajorana (k : ℕ) : MatStage (k + 1) :=
  globalChirality k ⊗ₖ chiralBipolar baseChiralMajorana

/-- The full-stage lift is exactly the repository's Jordan–Wigner Majorana
operator; the equality fixes the carrier transport without a coordinate
surrogate. -/
theorem liftedChiralMajorana_eq_majoranaDifference (k : ℕ) :
    liftedChiralMajorana k = majoranaDifference k := by
  unfold liftedChiralMajorana majoranaDifference jw_u_new jw_v_new
  rw [chiralBipolar_baseMajorana_eq]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  change globalChirality k i₁ j₁ * baseChiralMajorana i₂ j₂ =
    globalChirality k i₁ j₁ * a_dagger_base i₂ j₂ -
      globalChirality k i₁ j₁ * a_base i₂ j₂
  simp only [baseChiralMajorana, Matrix.sub_apply]
  ring_nf

/-- The lifted chiral generator is genuinely skew on the full stage carrier. -/
theorem liftedChiralMajorana_skew (k : ℕ) :
    (liftedChiralMajorana k)ᵀ = -liftedChiralMajorana k := by
  rw [liftedChiralMajorana_eq_majoranaDifference]
  exact majoranaDifference_skew k

/-- The lifted chiral generator is nonzero on every finite tensor stage. -/
theorem liftedChiralMajorana_ne_zero (k : ℕ) :
    liftedChiralMajorana k ≠ 0 := by
  rw [liftedChiralMajorana_eq_majoranaDifference]
  exact majoranaDifference_ne_zero k

/-- On the full tensor stage the lifted chiral generator anticommutes with
the stage chirality operator. This identifies its Peirce-sector-changing
action in the same carrier used by the Markov dissipative operator. -/
theorem liftedChiralMajorana_anticommutes_globalChirality (k : ℕ) :
    globalChirality (k + 1) * liftedChiralMajorana k +
      liftedChiralMajorana k * globalChirality (k + 1) = 0 := by
  have hbase : gamma_chiral_base * baseChiralMajorana +
      baseChiralMajorana * gamma_chiral_base = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
        InfoGeometry.Clifford.Cl11Matrix.J1,
        InfoGeometry.Clifford.Cl11Matrix.Eminus,
        baseChiralMajorana, a_dagger_base, a_base,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hstage : globalChirality (k + 1) =
      globalChirality k ⊗ₖ gamma_chiral_base := rfl
  rw [hstage]
  unfold liftedChiralMajorana
  rw [chiralBipolar_baseMajorana_eq]
  change (globalChirality k ⊗ₖ gamma_chiral_base) *
      (globalChirality k ⊗ₖ baseChiralMajorana) +
    (globalChirality k ⊗ₖ baseChiralMajorana) *
      (globalChirality k ⊗ₖ gamma_chiral_base) = 0
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq]
  rw [← Matrix.kronecker_add, hbase, Matrix.kronecker_zero]

/-- Symmetric-softmax dissipation and the lifted chiral bipolar reversible
action coexist on the full noncommutative matrix carrier. The group inverse
recovers the projected dissipative force, while the weighted chiral action
has zero pairing with the constant energy force. -/
theorem exists_symmetricSoftmax_groupInverse_liftedChiral_balance
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
        (mulLeftLinearMap (Idx (k + 1)) ℝ
            (weightedSkewActionMatrix
              (FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
              (liftedChiralMajorana k))
            (constantOneMatrix (ι := Idx (k + 1))) +
          markovLeftOnsager
            (FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
            entropyForce) = 0 ∧
      liftedChiralMajorana k ≠ 0 := by
  obtain ⟨G, hG, hRecover, hBalance⟩ :=
    exists_symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance
      scores hsymm entropyForce (liftedChiralMajorana k)
      (liftedChiralMajorana_skew k)
  exact ⟨G, hG, hRecover, hBalance, liftedChiralMajorana_ne_zero k⟩

end InfoGeometry.QuantumContext.MarkovDrazin.ChiralBipolarLift
