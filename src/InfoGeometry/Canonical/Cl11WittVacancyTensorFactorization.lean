import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.JordanWignerCAR

noncomputable section

open scoped Matrix Kronecker
open Matrix

namespace InfoGeometry.Canonical.Cl11WittVacancyTensorFactorization

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.JordanWignerCAR

/-- Local one-mode vacancy projector `a a†`. -/
def localVacancyProjector : Matrix (Fin 2) (Fin 2) ℝ :=
  wittAnnihilationBase * wittCreationBase

/-- The local vacancy projector is the second coordinate projector. -/
theorem localVacancyProjector_eq :
    localVacancyProjector = !![(0 : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localVacancyProjector, wittAnnihilationBase,
      wittCreationBase, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite-stage vacancy projector at one Jordan--Wigner site. -/
def vacancyAt (n : ℕ) (k : Fin n) : MatStage n :=
  jwAnnihilation n k * jwCreation n k

/--
Tensor-coordinate realization of a vacancy projector: identity on every site
except the chosen site, where the local vacancy projector is inserted.
-/
noncomputable def vacancyTensorAt : (n : ℕ) → Fin n → MatStage n
  | 0, k => Fin.elim0 k
  | n + 1, k =>
      if h : (k : ℕ) < n then
        vacancyTensorAt n ⟨k, h⟩ ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)
      else
        (1 : MatStage n) ⊗ₖ localVacancyProjector

/--
A Jordan--Wigner vacancy projector has no residual chirality string.
The two strings cancel because `globalChirality n ^ 2 = 1`.
-/
theorem vacancyAt_eq_tensor :
    ∀ (n : ℕ) (k : Fin n), vacancyAt n k = vacancyTensorAt n k
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := vacancyAt_eq_tensor n k'
        simp [vacancyAt, jwAnnihilation, jwCreation,
          jwStringWithBase, vacancyTensorAt, h]
        change
          ((jwStringWithBase wittAnnihilationBase n k' ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
            (jwStringWithBase wittCreationBase n k' ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ))) =
          vacancyTensorAt n k' ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
        exact congrArg (fun A : MatStage n => A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        simp [vacancyAt, jwAnnihilation, jwCreation,
          jwStringWithBase, vacancyTensorAt]
        change
          (globalChirality n ⊗ₖ wittAnnihilationBase) *
              (globalChirality n ⊗ₖ wittCreationBase) =
            (1 : MatStage n) ⊗ₖ localVacancyProjector
        rw [← Matrix.mul_kronecker_mul, globalChirality_sq]
        rfl

/-- The last-site vacancy projector is exactly `1 ⊗ p_vac`. -/
theorem vacancyAt_last (n : ℕ) :
    vacancyAt (n + 1) (Fin.last n) =
      (1 : MatStage n) ⊗ₖ localVacancyProjector := by
  rw [vacancyAt_eq_tensor]
  simp [vacancyTensorAt]
  rfl

end InfoGeometry.Canonical.Cl11WittVacancyTensorFactorization
