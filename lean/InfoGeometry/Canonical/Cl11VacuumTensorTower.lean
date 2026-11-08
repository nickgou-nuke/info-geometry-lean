import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11WittVacancyTensorFactorization

noncomputable section

open scoped Matrix Kronecker
open Matrix

namespace InfoGeometry.Canonical.Cl11VacuumTensorTower

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11WittVacancyTensorFactorization

/-- Recursive finite-stage Fock-vacuum projector. -/
noncomputable def vacuumTower : (n : ℕ) → MatStage n
  | 0 => 1
  | n + 1 =>
      matStageEmbed n (vacuumTower n) * vacancyAt (n + 1) (Fin.last n)

/-- The recursive vacuum projector is the pure tensor power of the local vacancy projector. -/
theorem vacuumTower_eq_kronPow :
    ∀ n : ℕ, vacuumTower n = kronPow localVacancyProjector n
  | 0 => rfl
  | n + 1 => by
      rw [vacuumTower, vacancyAt_last, vacuumTower_eq_kronPow n]
      change
        ((kronPow localVacancyProjector n) ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          ((1 : MatStage n) ⊗ₖ localVacancyProjector) =
        kronPow localVacancyProjector (n + 1)
      rw [← Matrix.mul_kronecker_mul]
      simp [kronPow]

/-- The local vacancy projector is idempotent. -/
theorem localVacancyProjector_idempotent :
    localVacancyProjector * localVacancyProjector = localVacancyProjector := by
  rw [localVacancyProjector_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Every tensor power of the local vacancy projector is idempotent. -/
theorem kronPow_localVacancyProjector_idempotent :
    ∀ n : ℕ,
      kronPow localVacancyProjector n * kronPow localVacancyProjector n =
        kronPow localVacancyProjector n
  | 0 => by simp [kronPow]
  | n + 1 => by
      change
        (kronPow localVacancyProjector n ⊗ₖ localVacancyProjector) *
            (kronPow localVacancyProjector n ⊗ₖ localVacancyProjector) =
          kronPow localVacancyProjector n ⊗ₖ localVacancyProjector
      rw [← Matrix.mul_kronecker_mul,
        kronPow_localVacancyProjector_idempotent n,
        localVacancyProjector_idempotent]

/-- The recursive vacuum is idempotent at every finite stage. -/
theorem vacuumTower_idempotent (n : ℕ) :
    vacuumTower n * vacuumTower n = vacuumTower n := by
  rw [vacuumTower_eq_kronPow]
  exact kronPow_localVacancyProjector_idempotent n

end InfoGeometry.Canonical.Cl11VacuumTensorTower
