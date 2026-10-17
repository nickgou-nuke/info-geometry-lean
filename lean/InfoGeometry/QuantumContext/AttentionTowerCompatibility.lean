/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionStageColimitState
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
import Mathlib.Tactic

/-!
# Coherent attention data on the dyadic matrix tower

Duplicating a finite logit vector along the new tensor factor makes the
scaled softmax density compatible with the canonical successor embedding
`A ↦ A ⊗ₖ 1`. The identity is stated in the full complex matrix carrier.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionTowerCompatibility

open BigOperators
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge
open InfoGeometry.Clifford.JordanWignerBridge
open scoped Kronecker

/-- Repeat each stage-`k` logit on the two basis vectors of the new tensor
factor. -/
def liftLogits (k : ℕ) (logits : Fin (2 ^ k) → ℝ) :
    Fin (2 ^ (k + 1)) → ℝ :=
  fun j => logits ((stageIndexEquiv k).symm j).1

private theorem liftedSoftmax_denominator (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    (∑ j : Fin (2 ^ (k + 1)), Real.exp (β * liftLogits k logits j)) =
      2 * ∑ i : Fin (2 ^ k), Real.exp (β * logits i) := by
  rw [show (∑ j : Fin (2 ^ (k + 1)),
      Real.exp (β * liftLogits k logits j)) =
        ∑ p : Fin (2 ^ k) × Fin 2, Real.exp (β * logits p.1) by
          unfold liftLogits
          exact Equiv.sum_comp (stageIndexEquiv k).symm
            (fun p : Fin (2 ^ k) × Fin 2 => Real.exp (β * logits p.1))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  calc
    (∑ i : Fin (2 ^ k),
        (Real.exp (β * logits i) + Real.exp (β * logits i))) =
        ∑ i : Fin (2 ^ k), 2 * Real.exp (β * logits i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 2 * ∑ i : Fin (2 ^ k), Real.exp (β * logits i) := by
          rw [Finset.mul_sum]

/-- Duplicating logits splits each softmax weight equally between the two
coordinates of the newly adjoined tensor factor. -/
theorem softmaxWeight_lift_eq_half (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (i : Fin (2 ^ k)) (a : Fin 2) :
    softmaxWeight (liftLogits k logits) β (stageIndexEquiv k (i, a)) =
      softmaxWeight logits β i / 2 := by
  unfold softmaxWeight
  rw [liftedSoftmax_denominator]
  have hden : (∑ j : Fin (2 ^ k), Real.exp (β * logits j)) ≠ 0 := by
    have hpos : 0 < ∑ j : Fin (2 ^ k), Real.exp (β * logits j) := by
      apply Finset.sum_pos'
      · intro j hj
        exact le_of_lt (Real.exp_pos _)
      · exact ⟨0, Finset.mem_univ _, Real.exp_pos _⟩
    exact ne_of_gt hpos
  simp only [liftLogits, Equiv.symm_apply_apply]
  field_simp [hden]

private theorem concreteStep_diagonal (k : ℕ)
    (d : Fin (2 ^ k) → ℂ) :
    concreteStep k (Matrix.diagonal d) =
      Matrix.diagonal (fun j => d ((stageIndexEquiv k).symm j).1) := by
  ext i j
  cases hi : (stageIndexEquiv k).symm i with
  | mk i₁ i₂ =>
    cases hj : (stageIndexEquiv k).symm j with
    | mk j₁ j₂ =>
      have hi' : i = stageIndexEquiv k (i₁, i₂) := by
        calc
          i = stageIndexEquiv k ((stageIndexEquiv k).symm i) :=
            ((stageIndexEquiv k).apply_symm_apply i).symm
          _ = stageIndexEquiv k (i₁, i₂) := congrArg (stageIndexEquiv k) hi
      have hj' : j = stageIndexEquiv k (j₁, j₂) := by
        calc
          j = stageIndexEquiv k ((stageIndexEquiv k).symm j) :=
            ((stageIndexEquiv k).apply_symm_apply j).symm
          _ = stageIndexEquiv k (j₁, j₂) := congrArg (stageIndexEquiv k) hj
      rw [hi', hj']
      change (Matrix.reindex (stageIndexEquiv k) (stageIndexEquiv k)
        ((Matrix.diagonal d) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))
          (stageIndexEquiv k (i₁, i₂)) (stageIndexEquiv k (j₁, j₂)) = _
      by_cases hfirst : i₁ = j₁ <;> by_cases hlast : i₂ = j₂ <;>
        simp [Matrix.reindex, hfirst, hlast]

/-- The diagonal modular unitary is carried to the successor stage when the
logits are duplicated on the new tensor coordinate. -/
theorem modularUnitary_lift_compatible (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) :
    modularUnitary (liftLogits k logits) β t =
      concreteStep k (modularUnitary logits β t) := by
  change Matrix.diagonal (modularPhase (liftLogits k logits) β t) =
    concreteStep k (Matrix.diagonal (modularPhase logits β t))
  rw [concreteStep_diagonal]
  ext j l
  by_cases hjl : j = l
  · subst l
    simp only [Matrix.diagonal_apply]
    cases hpair : (stageIndexEquiv k).symm j with
    | mk i a =>
        have hj : j = stageIndexEquiv k (i, a) := by
          calc
            j = stageIndexEquiv k ((stageIndexEquiv k).symm j) :=
              ((stageIndexEquiv k).apply_symm_apply j).symm
            _ = stageIndexEquiv k (i, a) := congrArg (stageIndexEquiv k) hpair
        subst j
        simp [modularPhase, liftLogits]
  · simp [hjl]

/-- The dimension-scaled softmax density is compatible with the actual
noncommutative dyadic matrix successor embedding when logits are lifted by
duplication. -/
theorem attentionStageDensity_lift_compatible (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    attentionStageDensity (k + 1) (liftLogits k logits) β =
      concreteStep k (attentionStageDensity k logits β) := by
  change Matrix.diagonal
      (fun j => (2 ^ (k + 1) : ℂ) *
        (softmaxWeight (liftLogits k logits) β j : ℂ)) =
    concreteStep k (Matrix.diagonal
      (fun i => (2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ)))
  rw [concreteStep_diagonal]
  ext j l
  by_cases hjl : j = l
  · subst l
    simp only [Matrix.diagonal_apply]
    cases hpair : (stageIndexEquiv k).symm j with
    | mk i a =>
        have hj : j = stageIndexEquiv k (i, a) := by
          calc
            j = stageIndexEquiv k ((stageIndexEquiv k).symm j) :=
              ((stageIndexEquiv k).apply_symm_apply j).symm
            _ = stageIndexEquiv k (i, a) := congrArg (stageIndexEquiv k) hpair
        subst j
        rw [softmaxWeight_lift_eq_half]
        push_cast
        norm_num [pow_succ, Nat.mul_comm]
        ring
  · simp [hjl]

/-- The full noncommutative modular automorphism intertwines the actual
successor *-algebra embedding under the same duplicated-logit transport. -/
theorem modularFlow_lift_intertwines_concreteStep (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A : MatrixStage k) :
    concreteStep k (modularFlow logits β t A) =
      modularFlow (liftLogits k logits) β t (concreteStep k A) := by
  unfold modularFlow
  rw [map_mul, map_mul, modularUnitary_lift_compatible,
    modularUnitary_lift_compatible]

/-! ### Last-mode modular eigenoperators on the actual Cl(1,1) tower -/

/-- Diagonal entries of the one-site chiral parity matrix. -/
private def chiralBaseDiagonal : Fin 2 → ℝ
  | 0 => -1
  | 1 => 1

private theorem gamma_chiral_base_eq_diagonal :
    gamma_chiral_base = Matrix.diagonal chiralBaseDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus, chiralBaseDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Recursive diagonal values of the product chiral operator on the tensor
index `Idx n`. -/
private def chiralTowerDiagonal : (n : ℕ) → InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ
  | 0, _ => 1
  | n + 1, (i, b) =>
      chiralTowerDiagonal n i * chiralBaseDiagonal b

/-- The actual tensor-tower chirality is diagonal at every finite stage. -/
private theorem globalChirality_eq_diagonal (n : ℕ) :
    globalChirality n = Matrix.diagonal (chiralTowerDiagonal n) := by
  induction n with
  | zero =>
      ext i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp [globalChirality, InfoGeometry.Clifford.TowerMatrix.kronPow, chiralTowerDiagonal,
        Matrix.diagonal_apply]
  | succ n ih =>
      have ih' : InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n =
          Matrix.diagonal (chiralTowerDiagonal n) := by
        simpa [globalChirality] using ih
      change InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base (n + 1) = _
      rw [show InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base (n + 1) =
        InfoGeometry.Clifford.TowerMatrix.kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base by rfl,
        ih', gamma_chiral_base_eq_diagonal,
        Matrix.diagonal_kronecker_diagonal]
      rfl

private theorem globalChirality_complexify_eq_diagonal (n : ℕ) :
    (algebraMap ℝ ℂ).mapMatrix (globalChirality n) =
      Matrix.diagonal (fun i => (chiralTowerDiagonal n i : ℂ)) := by
  rw [globalChirality_eq_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [RingHom.mapMatrix_apply, Matrix.diagonal_apply]
  · simp [RingHom.mapMatrix_apply, Matrix.diagonal_apply, h]

/-! ### Modular action on the newly introduced Jordan--Wigner mode -/

/-- Add an energy increment to the occupied coordinate of the appended mode. -/
def occupiedEnergyLift (k : ℕ)
    (logits : InfoGeometry.Clifford.TowerMatrix.Idx k → ℝ) (ε : ℝ) :
    InfoGeometry.Clifford.TowerMatrix.Idx (k + 1) → ℝ :=
  fun p => logits p.1 + if p.2 = 1 then ε else 0

/-- The new Jordan--Wigner creation operator is an eigenoperator of the finite
modular flow when the appended occupation coordinate receives energy `ε`.
This statement is on the repository's recursive tensor index and actual
complexified Cl(1,1) Jordan--Wigner generator. -/
theorem jwNewCreate_occupiedEnergy_eigen_entry (k : ℕ)
    (logits : InfoGeometry.Clifford.TowerMatrix.Idx k → ℝ)
    (ε β t : ℝ)
    (i j : InfoGeometry.Clifford.TowerMatrix.Idx (k + 1)) :
    modularFlow (occupiedEnergyLift k logits ε) β t
      (complexifyClTensorStage (k + 1) (jw_u_new k)) i j =
      Complex.exp (-Complex.I * (t : ℂ) * (β : ℂ) * (ε : ℂ)) *
        (complexifyClTensorStage (k + 1) (jw_u_new k) i j) := by
  rw [modularFlow_apply_eq_exp_sub]
  by_cases hzero :
      complexifyClTensorStage (k + 1) (jw_u_new k) i j = 0
  · simp [hzero]
  · cases i with
    | mk i₁ i₂ =>
      cases j with
      | mk j₁ j₂ =>
        have hsupp : i₁ = j₁ ∧ i₂ = 0 ∧ j₂ = 1 := by
          have hentry :
              (algebraMap ℝ ℂ) ((jw_u_new k) (i₁, i₂) (j₁, j₂)) ≠ 0 := by
            change (algebraMap ℝ ℂ) ((jw_u_new k) (i₁, i₂) (j₁, j₂)) ≠ 0 at hzero
            exact hzero
          rw [jw_u_new, Matrix.kronecker_apply, globalChirality_eq_diagonal] at hentry
          simp [Matrix.diagonal_apply, a_dagger_base] at hentry
          rcases hentry with ⟨hprefix, hchirality, hlocal⟩
          have hbits : i₂ = 0 ∧ j₂ = 1 := by
            fin_cases i₂ <;> fin_cases j₂ <;> simp_all [a_dagger_base]
          exact ⟨hprefix, hbits.1, hbits.2⟩
        have hgap : occupiedEnergyLift k logits ε (i₁, i₂) -
            occupiedEnergyLift k logits ε (j₁, j₂) = -ε := by
          simp [occupiedEnergyLift, hsupp.1, hsupp.2.1, hsupp.2.2]
        rw [hgap]
        apply congrArg (fun z : ℂ =>
          z * complexifyClTensorStage (k + 1) (jw_u_new k) (i₁, i₂) (j₁, j₂))
        apply congrArg Complex.exp
        push_cast
        ring_nf

/-- Matrix form of the new creation eigenoperator identity. -/
theorem jwNewCreate_occupiedEnergy_eigen (k : ℕ)
    (logits : InfoGeometry.Clifford.TowerMatrix.Idx k → ℝ)
    (ε β t : ℝ) :
    modularFlow (occupiedEnergyLift k logits ε) β t
      (complexifyClTensorStage (k + 1) (jw_u_new k)) =
      Complex.exp (-Complex.I * (t : ℂ) * (β : ℂ) * (ε : ℂ)) •
        complexifyClTensorStage (k + 1) (jw_u_new k) := by
  ext i j
  rw [jwNewCreate_occupiedEnergy_eigen_entry]
  simp [Matrix.smul_apply]

end InfoGeometry.QuantumContext.AttentionTowerCompatibility
