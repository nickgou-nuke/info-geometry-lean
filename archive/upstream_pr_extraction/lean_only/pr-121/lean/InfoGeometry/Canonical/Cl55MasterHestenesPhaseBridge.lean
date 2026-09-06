import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11InfiniteCarrier
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

/-!
# Global Hestenes phase on the five-mode master carrier

The tower already contains the coherent head phase
`hestenesPhaseHead n : MatStage (n + 1)`.  This owner specializes that native
construction to the `Cl(5,5)` master carrier and proves its square directly.
It does not identify this master phase with the phase on the embedded doubled
three-mode subcarrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge

open Matrix
open scoped Kronecker
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

abbrev MasterMat32 := MatStage 5

noncomputable def masterHestenesPhase : MasterMat32 :=
  hestenesPhaseHead 4

theorem hestenesPhaseHead_stage_embed (n : ℕ) :
    matStageEmbed (n + 1) (hestenesPhaseHead n) =
      hestenesPhaseHead (n + 1) := by
  rfl

theorem hestenesPhaseHead_intoCarrier (n : ℕ) :
    intoCarrier (n + 1) (hestenesPhaseHead n) = globalPhaseAxis := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        intoCarrier (n + 1 + 1) (hestenesPhaseHead (n + 1)) =
            intoCarrier (n + 1 + 1)
              (matStageEmbed (n + 1) (hestenesPhaseHead n)) := by
                rfl
        _ = intoCarrier (n + 1) (hestenesPhaseHead n) := by
              rw [← InfoGeometry.Clifford.Cl11TensorTower.stageEmbed_apply]
              rw [← InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed_one_apply]
              exact intoCarrier_finiteAdvance (n + 1) 1 (hestenesPhaseHead n)
        _ = globalPhaseAxis := ih

theorem hestenesPhaseHead_sq :
    ∀ n : ℕ,
      hestenesPhaseHead n * hestenesPhaseHead n =
        -(1 : MatStage (n + 1))
  | 0 => by
      change kronPow hestenesPhaseBase 1 * kronPow hestenesPhaseBase 1 =
        -(1 : MatStage 1)
      dsimp [kronPow]
      rw [← Matrix.mul_kronecker_mul, hestenesPhaseBase_sq]
      ext i j
      cases i with
      | mk i0 i1 =>
          cases j with
          | mk j0 j1 =>
              have h0 : i0 = j0 := Subsingleton.elim _ _
              subst h0
              fin_cases i0
              fin_cases i1 <;> fin_cases j1 <;> simp
  | n + 1 => by
      change (hestenesPhaseHead n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (hestenesPhaseHead n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        -(1 : MatStage (n + 2))
      rw [← Matrix.mul_kronecker_mul, hestenesPhaseHead_sq n]
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · by_cases h1 : i.1 = j.1
        · have h2 : i.2 ≠ j.2 := by
            intro h2
            apply hij
            exact Prod.ext h1 h2
          simp [Matrix.neg_apply, hij, h1, h2]
        · simp [Matrix.neg_apply, Matrix.one_apply, hij, h1]

theorem hestenesPhaseBase_anticomm_gammaChiralBase :
    hestenesPhaseBase * gamma_chiral_base +
        gamma_chiral_base * hestenesPhaseBase = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [hestenesPhaseBase, gamma_chiral_base, gamma_0_base,
      gamma_1_base, InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus, Matrix.mul_apply,
      Matrix.add_apply, Fin.sum_univ_two]

theorem hestenesPhaseBase_creation_residual :
    hestenesPhaseBase * wittCreationBase +
        wittCreationBase * hestenesPhaseBase = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [hestenesPhaseBase, wittCreationBase, Matrix.mul_apply,
      Matrix.add_apply, Fin.sum_univ_two]

theorem hestenesPhaseBase_annihilation_residual :
    hestenesPhaseBase * wittAnnihilationBase +
        wittAnnihilationBase * hestenesPhaseBase = -1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [hestenesPhaseBase, wittAnnihilationBase, Matrix.mul_apply,
      Matrix.add_apply, Fin.sum_univ_two]

theorem hestenesPhaseHead_anticomm_globalChirality :
    ∀ n : ℕ,
      hestenesPhaseHead n * globalChirality (n + 1) +
          globalChirality (n + 1) * hestenesPhaseHead n = 0
  | 0 => by
      change kronPow hestenesPhaseBase 1 * kronPow gamma_chiral_base 1 +
          kronPow gamma_chiral_base 1 * kronPow hestenesPhaseBase 1 = 0
      dsimp [kronPow]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [mul_one]
      rw [← Matrix.kronecker_add]
      simpa using congrArg
        (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
          (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ A)
        hestenesPhaseBase_anticomm_gammaChiralBase
  | n + 1 => by
      change (hestenesPhaseHead n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (kronPow gamma_chiral_base (n + 1) ⊗ₖ gamma_chiral_base) +
          (kronPow gamma_chiral_base (n + 1) ⊗ₖ gamma_chiral_base) *
            (hestenesPhaseHead n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [one_mul, mul_one]
      rw [← Matrix.add_kronecker]
      simpa [globalChirality] using congrArg
        (fun A : MatStage (n + 1) => A ⊗ₖ gamma_chiral_base)
        (hestenesPhaseHead_anticomm_globalChirality n)

theorem masterHestenesPhase_sq :
    masterHestenesPhase * masterHestenesPhase =
      -(1 : MasterMat32) := by
  exact hestenesPhaseHead_sq 4

/-! The finite Hodge packet has scalar square, so the concrete phase commutes
with its square without any unproved phase--Dirac oddness assumption. -/
theorem masterHestenesPhase_commutes_hodgeDirac_square :
    masterHestenesPhase *
          (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) =
      (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) *
        masterHestenesPhase := by
  rw [embeddedSplitOctonionHodgeDirac_sq]
  simp

theorem masterHestenesPhase_anticomm_chirality :
    masterHestenesPhase * globalChirality 5 +
        globalChirality 5 * masterHestenesPhase = 0 := by
  exact hestenesPhaseHead_anticomm_globalChirality 4

theorem masterHestenesPhase_mul_chiralProjPlus :
    masterHestenesPhase * chiralProjPlus 5 =
      chiralProjMinus 5 * masterHestenesPhase := by
  have h := masterHestenesPhase_anticomm_chirality
  dsimp [chiralProjPlus, chiralProjMinus]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_add, sub_mul, mul_one, one_mul]
  rw [eq_neg_of_add_eq_zero_left h]
  noncomm_ring

theorem masterHestenesPhase_mul_chiralProjMinus :
    masterHestenesPhase * chiralProjMinus 5 =
      chiralProjPlus 5 * masterHestenesPhase := by
  have h := masterHestenesPhase_anticomm_chirality
  dsimp [chiralProjPlus, chiralProjMinus]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_sub, add_mul, mul_one, one_mul]
  rw [eq_neg_of_add_eq_zero_left h]
  noncomm_ring

theorem masterHestenesPhase_mul_chiralProjPlus_mul_phase :
    masterHestenesPhase * chiralProjPlus 5 * masterHestenesPhase =
      -(chiralProjMinus 5) := by
  calc
    masterHestenesPhase * chiralProjPlus 5 * masterHestenesPhase =
        (chiralProjMinus 5 * masterHestenesPhase) * masterHestenesPhase := by
          rw [masterHestenesPhase_mul_chiralProjPlus]
    _ = chiralProjMinus 5 *
          (masterHestenesPhase * masterHestenesPhase) := by
          rw [mul_assoc]
    _ = -(chiralProjMinus 5) := by
          rw [masterHestenesPhase_sq]
          simp

theorem masterHestenesPhase_mul_chiralProjMinus_mul_phase :
    masterHestenesPhase * chiralProjMinus 5 * masterHestenesPhase =
      -(chiralProjPlus 5) := by
  calc
    masterHestenesPhase * chiralProjMinus 5 * masterHestenesPhase =
        (chiralProjPlus 5 * masterHestenesPhase) * masterHestenesPhase := by
          rw [masterHestenesPhase_mul_chiralProjMinus]
    _ = chiralProjPlus 5 *
          (masterHestenesPhase * masterHestenesPhase) := by
          rw [mul_assoc]
    _ = -(chiralProjPlus 5) := by
          rw [masterHestenesPhase_sq]
          simp

end InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge
