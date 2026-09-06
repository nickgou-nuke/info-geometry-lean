import InfoGeometry.Canonical.Cl11TensorTowerLocalParity
import InfoGeometry.Clifford.JordanWignerCAR

set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl11TensorTowerGlobalParity

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Canonical.Cl11TensorTowerLocalParity

theorem globalChirality_anticomm_jwCreation :
    ∀ (n : ℕ) (k : Fin n),
      globalChirality n * jwCreation n k +
        jwCreation n k * globalChirality n = 0
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := globalChirality_anticomm_jwCreation n k'
        simp only [globalChirality, jwCreation, jwStringWithBase, h]
        change (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) *
            ((jwStringWithBase wittCreationBase n k') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
          ((jwStringWithBase wittCreationBase n k') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
            (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) = 0
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
        simp only [mul_one, one_mul]
        rw [← Matrix.add_kronecker]
        simpa [globalChirality] using
          congrArg (fun A : MatStage n => A ⊗ₖ gamma_chiral_base) ih
      · have hk_eq : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        simp [globalChirality, jwCreation, jwStringWithBase]
        change (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) *
            (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) +
          (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) *
            (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) = 0
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
        rw [← Matrix.kronecker_add]
        have hsq : kronPow gamma_chiral_base n * kronPow gamma_chiral_base n =
            (1 : MatStage n) := by
          simpa [globalChirality] using globalChirality_sq n
        rw [hsq]
        simpa using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
          (1 : MatStage n) ⊗ₖ A)
          gamma_chiral_base_anticomm_wittCreation

theorem globalChirality_anticomm_jwAnnihilation :
    ∀ (n : ℕ) (k : Fin n),
      globalChirality n * jwAnnihilation n k +
        jwAnnihilation n k * globalChirality n = 0
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := globalChirality_anticomm_jwAnnihilation n k'
        simp only [globalChirality, jwAnnihilation, jwStringWithBase, h]
        change (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) *
            ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
          ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
            (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) = 0
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
        simp only [mul_one, one_mul]
        rw [← Matrix.add_kronecker]
        simpa [globalChirality] using
          congrArg (fun A : MatStage n => A ⊗ₖ gamma_chiral_base) ih
      · have hk_eq : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        simp [globalChirality, jwAnnihilation, jwStringWithBase]
        change (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) *
            (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) +
          (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) *
            (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base) = 0
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
        rw [← Matrix.kronecker_add]
        have hsq : kronPow gamma_chiral_base n * kronPow gamma_chiral_base n =
            (1 : MatStage n) := by
          simpa [globalChirality] using globalChirality_sq n
        rw [hsq]
        simpa using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
          (1 : MatStage n) ⊗ₖ A)
          gamma_chiral_base_anticomm_wittAnnihilation

end InfoGeometry.Canonical.Cl11TensorTowerGlobalParity
