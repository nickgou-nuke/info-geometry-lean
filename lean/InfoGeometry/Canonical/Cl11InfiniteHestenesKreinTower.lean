import InfoGeometry.Canonical.InfiniteHestenesKrein
import InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge
import InfoGeometry.Clifford.Cl11InfiniteCarrier
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.JordanWignerCAR

/-!
# Concrete Hestenes--Krein tower over the native `Cl(1,1)` stages

This is the concrete finite-to-colimit instance of the generic algebraic
`HestenesKreinTower`.  The stages are shifted by one so that the native
head phase `hestenesPhaseHead n` lives in stage `n + 1`.

Only the phase-axis and algebraic Krein identities are installed here.  No
claim is made that this real matrix tower is definitionally the complex
`SheetMatrix` carrier or that its chiral projectors already form a natural
transformation.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11InfiniteHestenesKreinTower

open InfoGeometry.Canonical.InfiniteHestenesKrein
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open scoped Kronecker

abbrev Stage (n : ℕ) : Type :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage (n + 1)
abbrev Limit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

def bond (n : ℕ) : Stage n →+* Stage (n + 1) :=
  InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1) |>.toRingHom

def toLimit (n : ℕ) : Stage n →+* Limit :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1)

def phaseAxis (n : ℕ) : Stage n :=
  InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead n

def modularSignHead : (n : ℕ) → Stage n
  | 0 => InfoGeometry.Clifford.TowerMatrix.kronPow
      InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base 1
  | n + 1 => modularSignHead n ⊗ₖ
      (1 : Matrix (Fin 2) (Fin 2) ℝ)

def modularGenerator (n : ℕ) : Stage n := modularSignHead n

def modularWeight (n : ℕ) : Stage n := 1

theorem phase_modularSign_base_krein :
    phaseAxis 0 * modularGenerator 0 * phaseAxis 0 = modularGenerator 0 := by
  change
    (((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ hestenesPhaseBase) *
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_chiral_base)) *
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ hestenesPhaseBase) =
    (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_chiral_base
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hestenesPhaseBase_chiral_sandwich]
  simp

def tower : HestenesKreinTower (Stage := Stage) (Limit := Limit) where
  bond := bond
  toLimit := toLimit
  hcone := by
    intro n x
    exact InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage_apply_bond (n + 1) x
  phaseAxis := phaseAxis
  modularWeight := modularWeight
  modularGenerator := modularGenerator
  phaseAxis_sq_zero := by
    simpa [phaseAxis] using
      (InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge.hestenesPhaseHead_sq 0)
  modularWeight_comm_generator_zero := by simp [modularWeight, modularGenerator]
  generator_krein_selfadjoint_zero := phase_modularSign_base_krein
  phaseAxis_step := fun _ => rfl
  modularWeight_step := by intro n; simp [bond, modularWeight]
  modularGenerator_step := fun _ => rfl

theorem phaseAxis_bond (n : ℕ) :
    bond n (phaseAxis n) = phaseAxis (n + 1) := by
  rfl

theorem modularWeight_bond (n : ℕ) :
    bond n (modularWeight n) = modularWeight (n + 1) := by
  simp [bond, modularWeight]

theorem modularGenerator_bond (n : ℕ) :
    bond n (modularGenerator n) = modularGenerator (n + 1) := by
  rfl

theorem modularGenerator_kreinSelfadjoint_all :
    ∀ n : ℕ,
      phaseAxis n * modularGenerator n * phaseAxis n = modularGenerator n := by
  exact HestenesKreinTower.generator_kreinSelfadjoint_all tower

theorem modularWeight_commutes_all :
    ∀ n : ℕ,
      modularWeight n * modularGenerator n =
        modularGenerator n * modularWeight n := by
  exact HestenesKreinTower.modularWeight_commutes_modularGenerator_all tower

theorem modularGenerator_square_all :
    ∀ n : ℕ, modularGenerator n * modularGenerator n = (1 : Stage n) := by
  intro n
  induction n with
  | zero =>
      change
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ
          InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base) *
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ
            InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base) = _
      rw [← Matrix.mul_kronecker_mul,
        InfoGeometry.Clifford.JordanWignerCAR.gamma_chiral_base_sq]
      simp
  | succ n ih =>
      change
        (modularGenerator n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (modularGenerator n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = _
      rw [← Matrix.mul_kronecker_mul, ih]
      simp

def fPlus (n : ℕ) : Stage n :=
  (1 / 2 : ℝ) • (1 + modularGenerator n)

def fMinus (n : ℕ) : Stage n :=
  (1 / 2 : ℝ) • (1 - modularGenerator n)

theorem fPlus_idempotent (n : ℕ) : fPlus n * fPlus n = fPlus n := by
  simp only [fPlus, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, add_mul, mul_add]
  rw [modularGenerator_square_all n]
  module

theorem fMinus_idempotent (n : ℕ) : fMinus n * fMinus n = fMinus n := by
  simp only [fMinus, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, sub_mul, mul_sub]
  rw [modularGenerator_square_all n]
  module

theorem fPlus_mul_fMinus (n : ℕ) : fPlus n * fMinus n = 0 := by
  simp only [fPlus, fMinus, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, add_mul, mul_sub]
  rw [modularGenerator_square_all n]
  module

theorem fMinus_mul_fPlus (n : ℕ) : fMinus n * fPlus n = 0 := by
  simp only [fPlus, fMinus, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, mul_add, sub_mul]
  rw [modularGenerator_square_all n]
  module

theorem fPlus_add_fMinus (n : ℕ) : fPlus n + fMinus n = (1 : Stage n) := by
  simp [fPlus, fMinus]
  module

theorem fPlus_bond (n : ℕ) : bond n (fPlus n) = fPlus (n + 1) := by
  change InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1)
      ((1 / 2 : ℝ) • (1 + modularGenerator n)) =
    (1 / 2 : ℝ) • (1 + modularGenerator (n + 1))
  simp only [Algebra.smul_def, map_mul, map_add, map_one]
  have h := modularGenerator_bond n
  change InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1)
      (modularGenerator n) = modularGenerator (n + 1) at h
  rw [h]
  simp [Algebra.commutes]

theorem fMinus_bond (n : ℕ) : bond n (fMinus n) = fMinus (n + 1) := by
  change InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1)
      ((1 / 2 : ℝ) • (1 - modularGenerator n)) =
    (1 / 2 : ℝ) • (1 - modularGenerator (n + 1))
  simp only [Algebra.smul_def, map_mul, map_sub, map_one]
  have h := modularGenerator_bond n
  change InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + 1)
      (modularGenerator n) = modularGenerator (n + 1) at h
  rw [h]
  simp [Algebra.commutes]

theorem phaseAxis_square_all :
    ∀ n : ℕ, phaseAxis n * phaseAxis n = -(1 : Stage n) := by
  exact HestenesKreinTower.phaseAxis_square_all tower

theorem phaseAxis_limit_image (n : ℕ) :
    toLimit n (phaseAxis n) = toLimit 0 (phaseAxis 0) := by
  exact HestenesKreinTower.phaseAxis_limit_image tower n

theorem colimit_phaseAxis_square :
    (toLimit 0 (phaseAxis 0)) * (toLimit 0 (phaseAxis 0)) = -(1 : Limit) := by
  rw [← map_mul]
  simpa using congrArg (toLimit 0) (tower.phaseAxis_sq_zero)

end InfoGeometry.Canonical.Cl11InfiniteHestenesKreinTower
