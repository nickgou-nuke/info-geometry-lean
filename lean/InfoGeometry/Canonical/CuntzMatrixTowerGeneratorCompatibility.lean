import Mathlib.Data.Matrix.Basis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit

/-! Finite matrix units in the canonical complex UHF tower. -/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit

open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

def matrixUnit (n : ℕ) (i j : Fin (2 ^ n)) : MatrixStage n :=
  Matrix.single i j 1

@[simp] theorem matrixUnit_apply_same (n : ℕ) (i j : Fin (2 ^ n)) :
    matrixUnit n i j i j = 1 := by
  exact Matrix.single_apply_same i j 1

@[simp] theorem matrixUnit_mul_same (n : ℕ) (i j k : Fin (2 ^ n)) :
    matrixUnit n i j * matrixUnit n j k = matrixUnit n i k := by
  dsimp [matrixUnit]
  rw [Matrix.single_mul_single_same]
  simp

@[simp] theorem matrixUnit_mul_of_ne (n : ℕ) (i j k l : Fin (2 ^ n))
    (h : j ≠ k) :
    matrixUnit n i j * matrixUnit n k l = 0 := by
  dsimp [matrixUnit]
  exact Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i j k h 1

@[simp] theorem concreteMap_succ_step (n : ℕ) (x : MatrixStage n) :
    concreteMap (Nat.le_succ n) x = concreteStep n x := by
  change map concreteData (Nat.le.step (le_refl n)) x = concreteStep n x
  rw [map_succ concreteData (le_refl n)]
  dsimp [concreteData]
  rw [map_id]
  rfl

theorem stageInjection_matrixUnit_succ (n : ℕ) (i j : Fin (2 ^ n)) :
    stageInjection (n + 1)
        (concreteStep n (matrixUnit n i j)) =
      stageInjection n (matrixUnit n i j) := by
  rw [← concreteMap_succ_step n]
  exact stageInjection_concrete_transition (Nat.le_succ n) (matrixUnit n i j)

end InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
