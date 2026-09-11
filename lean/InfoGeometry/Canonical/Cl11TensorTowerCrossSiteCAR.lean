import InfoGeometry.Canonical.Cl11TensorTowerGlobalParity
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11TensorTowerGlobalParity

theorem creation_cross_site_anticommute :
    ∀ (n : ℕ) (i j : Fin n), i ≠ j →
      jwCreation n i * jwCreation n j +
        jwCreation n j * jwCreation n i = 0
  | 0, i, j, hij => Fin.elim0 i
  | n + 1, i, j, hij => by
      by_cases hi : (i : ℕ) < n
      · by_cases hj : (j : ℕ) < n
        · let i' : Fin n := ⟨i, hi⟩
          let j' : Fin n := ⟨j, hj⟩
          have hij' : i' ≠ j' := by
            intro h
            apply hij
            exact Fin.ext (by simpa [i', j'] using congrArg Fin.val h)
          have ih := creation_cross_site_anticommute n i' j' hij'
          simp [jwCreation, jwStringWithBase, hi, hj]
          change
            ((jwStringWithBase wittCreationBase n i') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                ((jwStringWithBase wittCreationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
              ((jwStringWithBase wittCreationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                ((jwStringWithBase wittCreationBase n i') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          rw [← Matrix.add_kronecker]
          simpa using congrArg (fun A : MatStage n => A ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
        · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
          subst j
          simp [jwCreation, jwStringWithBase, hi]
          change
            ((jwStringWithBase wittCreationBase n ⟨i, hi⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) +
              (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) *
                ((jwStringWithBase wittCreationBase n ⟨i, hi⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          simp only [one_mul, mul_one]
          rw [← Matrix.add_kronecker]
          have hp := globalChirality_anticomm_jwCreation n ⟨i, hi⟩
          simpa [add_comm, globalChirality, jwCreation] using
            congrArg (fun A : MatStage n => A ⊗ₖ wittCreationBase) hp
      · have hi_last : i = Fin.last n := Fin.eq_last_of_not_lt hi
        subst i
        by_cases hj : (j : ℕ) < n
        · let j' : Fin n := ⟨j, hj⟩
          have hne : Fin.last n ≠ j := hij
          simp [jwCreation, jwStringWithBase, hj]
          change
            (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) *
                ((jwStringWithBase wittCreationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
              ((jwStringWithBase wittCreationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          simp only [one_mul, mul_one]
          rw [← Matrix.add_kronecker]
          have hp := globalChirality_anticomm_jwCreation n ⟨j, hj⟩
          simpa using congrArg (fun A : MatStage n => A ⊗ₖ wittCreationBase) hp
        · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
          subst j
          exact (hij rfl).elim

theorem annihilation_cross_site_anticommute :
    ∀ (n : ℕ) (i j : Fin n), i ≠ j →
      jwAnnihilation n i * jwAnnihilation n j +
        jwAnnihilation n j * jwAnnihilation n i = 0
  | 0, i, j, hij => Fin.elim0 i
  | n + 1, i, j, hij => by
      by_cases hi : (i : ℕ) < n
      · by_cases hj : (j : ℕ) < n
        · let i' : Fin n := ⟨i, hi⟩
          let j' : Fin n := ⟨j, hj⟩
          have hij' : i' ≠ j' := by
            intro h
            apply hij
            exact Fin.ext (by simpa [i', j'] using congrArg Fin.val h)
          have ih := annihilation_cross_site_anticommute n i' j' hij'
          simp [jwAnnihilation, jwStringWithBase, hi, hj]
          change
            ((jwStringWithBase wittAnnihilationBase n i') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
              ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                ((jwStringWithBase wittAnnihilationBase n i') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            ← Matrix.add_kronecker]
          simpa using congrArg (fun A : MatStage n => A ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
        · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
          subst j
          simp [jwAnnihilation, jwStringWithBase, hi]
          change
            ((jwStringWithBase wittAnnihilationBase n ⟨i, hi⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) +
              (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) *
                ((jwStringWithBase wittAnnihilationBase n ⟨i, hi⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          simp only [one_mul, mul_one]
          rw [← Matrix.add_kronecker]
          have hp := globalChirality_anticomm_jwAnnihilation n ⟨i, hi⟩
          simpa [add_comm, globalChirality, jwAnnihilation] using
            congrArg (fun A : MatStage n => A ⊗ₖ wittAnnihilationBase) hp
      · have hi_last : i = Fin.last n := Fin.eq_last_of_not_lt hi
        subst i
        by_cases hj : (j : ℕ) < n
        · let j' : Fin n := ⟨j, hj⟩
          simp [jwAnnihilation, jwStringWithBase, hj]
          change
            (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) *
                ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
              ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          simp only [one_mul, mul_one]
          rw [← Matrix.add_kronecker]
          have hp := globalChirality_anticomm_jwAnnihilation n ⟨j, hj⟩
          simpa [globalChirality, jwAnnihilation] using
            congrArg (fun A : MatStage n => A ⊗ₖ wittAnnihilationBase) hp
        · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
          subst j
          exact (hij rfl).elim

theorem creation_annihilation_cross_site_anticommute :
    ∀ (n : ℕ) (i j : Fin n), i ≠ j →
      jwCreation n i * jwAnnihilation n j +
        jwAnnihilation n j * jwCreation n i = 0
  | 0, i, j, hij => Fin.elim0 i
  | n + 1, i, j, hij => by
      by_cases hi : (i : ℕ) < n
      · by_cases hj : (j : ℕ) < n
        · let i' : Fin n := ⟨i, hi⟩
          let j' : Fin n := ⟨j, hj⟩
          have hij' : i' ≠ j' := by
            intro h
            apply hij
            exact Fin.ext (by simpa [i', j'] using congrArg Fin.val h)
          have ih := creation_annihilation_cross_site_anticommute n i' j' hij'
          simp [jwCreation, jwAnnihilation, jwStringWithBase, hi, hj]
          change
            ((jwStringWithBase wittCreationBase n i') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
              ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                ((jwStringWithBase wittCreationBase n i') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            ← Matrix.add_kronecker]
          simpa using congrArg (fun A : MatStage n => A ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
        · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
          subst j
          simp [jwCreation, jwAnnihilation, jwStringWithBase, hi]
          change
            ((jwStringWithBase wittCreationBase n ⟨i, hi⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) +
              (kronPow gamma_chiral_base n ⊗ₖ wittAnnihilationBase) *
                ((jwStringWithBase wittCreationBase n ⟨i, hi⟩) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          simp only [one_mul, mul_one]
          rw [← Matrix.add_kronecker]
          have hp := globalChirality_anticomm_jwCreation n ⟨i, hi⟩
          simpa [add_comm, globalChirality, jwCreation] using
            congrArg (fun A : MatStage n => A ⊗ₖ wittAnnihilationBase) hp
      · have hi_last : i = Fin.last n := Fin.eq_last_of_not_lt hi
        subst i
        by_cases hj : (j : ℕ) < n
        · let j' : Fin n := ⟨j, hj⟩
          simp [jwCreation, jwAnnihilation, jwStringWithBase, hj]
          change
            (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) *
                ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
              ((jwStringWithBase wittAnnihilationBase n j') ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
                (kronPow gamma_chiral_base n ⊗ₖ wittCreationBase) = 0
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
          simp only [one_mul, mul_one]
          rw [← Matrix.add_kronecker]
          have hp := globalChirality_anticomm_jwAnnihilation n ⟨j, hj⟩
          simpa [globalChirality, jwAnnihilation] using
            congrArg (fun A : MatStage n => A ⊗ₖ wittCreationBase) hp
        · have hj_last : j = Fin.last n := Fin.eq_last_of_not_lt hj
          subst j
          exact (hij rfl).elim

theorem annihilation_creation_cross_site_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    jwAnnihilation n i * jwCreation n j +
      jwCreation n j * jwAnnihilation n i = 0 := by
  have h := creation_annihilation_cross_site_anticommute n j i (Ne.symm hij)
  simpa [add_comm] using h

theorem cross_site_CAR_profile
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    jwCreation n i * jwCreation n j +
        jwCreation n j * jwCreation n i = 0 ∧
      jwAnnihilation n i * jwAnnihilation n j +
        jwAnnihilation n j * jwAnnihilation n i = 0 ∧
      jwCreation n i * jwAnnihilation n j +
        jwAnnihilation n j * jwCreation n i = 0 ∧
      jwAnnihilation n i * jwCreation n j +
        jwCreation n j * jwAnnihilation n i = 0 := by
  exact ⟨creation_cross_site_anticommute n i j hij,
    annihilation_cross_site_anticommute n i j hij,
    creation_annihilation_cross_site_anticommute n i j hij,
    annihilation_creation_cross_site_anticommute n i j hij⟩

end InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
