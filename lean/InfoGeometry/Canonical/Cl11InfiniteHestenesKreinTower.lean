import InfoGeometry.Canonical.InfiniteHestenesKrein
import InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge
import InfoGeometry.Clifford.Cl11InfiniteCarrier
import InfoGeometry.Clifford.Cl11TensorTowerLimit

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
      InfoGeometry.Clifford.Cl11TensorTower.modularSignBase 1
  | n + 1 => modularSignHead n ⊗ₖ
      (1 : Matrix (Fin 2) (Fin 2) ℝ)

def modularGenerator (n : ℕ) : Stage n := modularSignHead n

def modularWeight (n : ℕ) : Stage n := 1

theorem phase_modularSign_base_krein :
    InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase *
        InfoGeometry.Clifford.Cl11TensorTower.modularSignBase *
        InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase =
      InfoGeometry.Clifford.Cl11TensorTower.modularSignBase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase,
      InfoGeometry.Clifford.Cl11TensorTower.modularSignBase,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus, Matrix.mul_apply,
      Fin.sum_univ_two]

def tower : HestenesKreinTower (Stage := Stage) (Limit := Limit) where
  bond := bond
  toLimit := toLimit
  phaseAxis := phaseAxis
  modularWeight := modularWeight
  modularGenerator := modularGenerator
  phaseAxis_sq_zero := by
    simpa [phaseAxis] using
      (InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge.hestenesPhaseHead_sq 0)
  modularWeight_comm_generator_zero := by simp [modularWeight, modularGenerator]
  generator_krein_selfadjoint_zero := by
    change InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead 0 *
      modularSignHead 0 *
      InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead 0 =
      modularSignHead 0
    dsimp [InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead,
      modularSignHead,
      InfoGeometry.Clifford.TowerMatrix.kronPow]
    change
      (((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ
          InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase) *
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ
          InfoGeometry.Clifford.Cl11TensorTower.modularSignBase)) *
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ
          InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ
        InfoGeometry.Clifford.Cl11TensorTower.modularSignBase
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      phase_modularSign_base_krein]
    simp

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
  exact HestenesKreinTower.generator_kreinSelfadjoint_all tower phaseAxis_bond
    modularGenerator_bond

theorem modularWeight_commutes_all :
    ∀ n : ℕ,
      modularWeight n * modularGenerator n =
        modularGenerator n * modularWeight n := by
  exact HestenesKreinTower.modularWeight_commutes_modularGenerator_all tower
    modularWeight_bond modularGenerator_bond

theorem phaseAxis_square_all :
    ∀ n : ℕ, phaseAxis n * phaseAxis n = -(1 : Stage n) := by
  exact HestenesKreinTower.phaseAxis_square_all tower phaseAxis_bond

theorem phaseAxis_limit_image (n : ℕ) :
    toLimit n (phaseAxis n) = toLimit 0 (phaseAxis 0) := by
  refine HestenesKreinTower.phaseAxis_limit_image tower n ?_ ?_
  · intro k x
    exact directLimitOf_bond
      (Stage := InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage)
      InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond (k + 1) x
  · exact phaseAxis_bond

theorem colimit_phaseAxis_square :
    (toLimit 0 (phaseAxis 0)) * (toLimit 0 (phaseAxis 0)) = -(1 : Limit) := by
  rw [← map_mul]
  simpa using congrArg (toLimit 0) (tower.phaseAxis_sq_zero)

end InfoGeometry.Canonical.Cl11InfiniteHestenesKreinTower
