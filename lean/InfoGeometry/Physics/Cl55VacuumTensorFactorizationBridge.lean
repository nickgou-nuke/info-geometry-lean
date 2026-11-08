import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11VacuumTensorTower
import InfoGeometry.Physics.Cl55VacuumMinimalIdealBridge

noncomputable section

open scoped Matrix Kronecker
open Matrix

namespace InfoGeometry.Physics.Cl55VacuumTensorFactorizationBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11WittVacancyTensorFactorization
open InfoGeometry.Canonical.Cl11VacuumTensorTower
open InfoGeometry.Physics.Cl55VacuumMinimalIdealBridge

theorem vacancyProjector_eq_vacancyAt (i : Fin 5) :
    vacancyProjector i = vacancyAt 5 i := by
  rfl

theorem vacuumProjector_eq_vacancy_product :
    vacuumProjector =
      (((vacancyAt 5 (0 : Fin 5) * vacancyAt 5 1) * vacancyAt 5 2) *
          vacancyAt 5 3) * vacancyAt 5 4 := by
  rfl

theorem matStageEmbed_vacancyAt {n : ℕ} (k : Fin n) :
    matStageEmbed n (vacancyAt n k) = vacancyAt (n + 1) k.castSucc := by
  dsimp [vacancyAt]
  simp [matStageEmbed_mul]

theorem vacuumTower_one : vacuumTower 1 = vacancyAt 1 0 := by
  change matStageEmbed 0 (vacuumTower 0) * vacancyAt 1 (Fin.last 0) = vacancyAt 1 0
  change matStageEmbed 0 1 * vacancyAt 1 0 = vacancyAt 1 0
  simp

theorem vacuumTower_two : vacuumTower 2 = vacancyAt 2 0 * vacancyAt 2 1 := by
  change matStageEmbed 1 (vacuumTower 1) * vacancyAt 2 (Fin.last 1) = vacancyAt 2 0 * vacancyAt 2 1
  rw [vacuumTower_one, matStageEmbed_vacancyAt]
  rfl

theorem vacuumTower_three :
    vacuumTower 3 = (vacancyAt 3 0 * vacancyAt 3 1) * vacancyAt 3 2 := by
  change matStageEmbed 2 (vacuumTower 2) * vacancyAt 3 (Fin.last 2) =
    (vacancyAt 3 0 * vacancyAt 3 1) * vacancyAt 3 2
  rw [vacuumTower_two, matStageEmbed_mul, matStageEmbed_vacancyAt, matStageEmbed_vacancyAt]
  rfl

theorem vacuumTower_four :
    vacuumTower 4 = ((vacancyAt 4 0 * vacancyAt 4 1) * vacancyAt 4 2) * vacancyAt 4 3 := by
  change matStageEmbed 3 (vacuumTower 3) * vacancyAt 4 (Fin.last 3) =
    ((vacancyAt 4 0 * vacancyAt 4 1) * vacancyAt 4 2) * vacancyAt 4 3
  rw [vacuumTower_three, matStageEmbed_mul, matStageEmbed_mul,
    matStageEmbed_vacancyAt, matStageEmbed_vacancyAt, matStageEmbed_vacancyAt]
  rfl

theorem vacuumTower_five :
    vacuumTower 5 = (((vacancyAt 5 0 * vacancyAt 5 1) * vacancyAt 5 2) * vacancyAt 5 3) * vacancyAt 5 4 := by
  change matStageEmbed 4 (vacuumTower 4) * vacancyAt 5 (Fin.last 4) =
    (((vacancyAt 5 0 * vacancyAt 5 1) * vacancyAt 5 2) * vacancyAt 5 3) * vacancyAt 5 4
  rw [vacuumTower_four, matStageEmbed_mul, matStageEmbed_mul, matStageEmbed_mul,
    matStageEmbed_vacancyAt, matStageEmbed_vacancyAt, matStageEmbed_vacancyAt, matStageEmbed_vacancyAt]
  rfl

theorem vacuumProjector_eq_vacuumTower_five :
    vacuumProjector = vacuumTower 5 := by
  rw [vacuumProjector_eq_vacancy_product, vacuumTower_five]

theorem vacuumProjector_eq_tensor_five :
    vacuumProjector = kronPow localVacancyProjector 5 := by
  rw [vacuumProjector_eq_vacuumTower_five, vacuumTower_eq_kronPow]

end InfoGeometry.Physics.Cl55VacuumTensorFactorizationBridge
