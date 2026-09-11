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

theorem vacuumProjector_eq_tensor_five :
    vacuumProjector = kronPow localVacancyProjector 5 := by
  rw [vacuumProjector_eq_vacancy_product]
  rw [vacancyAt_eq_tensor 5 (0 : Fin 5),
    vacancyAt_eq_tensor 5 (1 : Fin 5),
    vacancyAt_eq_tensor 5 (2 : Fin 5),
    vacancyAt_eq_tensor 5 (3 : Fin 5),
    vacancyAt_eq_tensor 5 (4 : Fin 5)]
  norm_num [vacancyTensorAt]
  repeat' rw [← Matrix.mul_kronecker_mul]
  simp [kronPow]

theorem vacuumProjector_eq_vacuumTower_five :
    vacuumProjector = vacuumTower 5 := by
  rw [vacuumProjector_eq_tensor_five, vacuumTower_eq_kronPow]

end InfoGeometry.Physics.Cl55VacuumTensorFactorizationBridge
