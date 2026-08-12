import Mathlib
import proofs.PeirceTensorQEC
import proofs.CuntzWordSpaceQEC

noncomputable section

open Matrix PeirceTensorQEC CuntzWordSpaceQEC
open scoped Kronecker

namespace CuntzPeirceLogicalCorner

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev Word2 := Fin 2 × Fin 2
abbrev Word2Matrix := Matrix Word2 Word2 ℂ

def logicalMatrixUnit (a b : Fin 2) : Word2Matrix :=
  fibonacciPeircePlusComplex ⊗ₖ Matrix.single a b (1 : ℂ)

theorem logicalMatrixUnit_error_compression
    {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (r s t u : Fin 2)
    (α β : ι) :
    logicalMatrixUnit r s *
        (firstFactorError F α)ᴴ *
        firstFactorError F β *
        logicalMatrixUnit t u =
      if s = t then
        (((F α)ᴴ * F β * fibonacciPeircePlusComplex).trace) •
          logicalMatrixUnit r u
      else 0 := by
  have hsingle :
      Matrix.single r s (1 : ℂ) * Matrix.single t u 1 =
        if s = t then Matrix.single r u 1 else 0 := by
    by_cases hst : s = t
    · subst t
      ext i j
      fin_cases r <;> fin_cases s <;> fin_cases u <;>
        fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.single,
          Fin.sum_univ_two]
    · ext i j
      fin_cases r <;> fin_cases s <;> fin_cases t <;> fin_cases u <;>
        fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.single,
          Fin.sum_univ_two, hst]
  simp only [logicalMatrixUnit, firstFactorError, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker (F α)
    (1 : Matrix (Fin 2) (Fin 2) ℂ)]
  rw [Matrix.conjTranspose_one]
  change Matrix.kronecker fibonacciPeircePlusComplex (Matrix.single r s 1) *
      Matrix.kronecker ((F α)ᴴ) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.kronecker (F β) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.kronecker fibonacciPeircePlusComplex (Matrix.single t u 1) = _
  have hmul1 :
      Matrix.kronecker fibonacciPeircePlusComplex (Matrix.single r s 1) *
          Matrix.kronecker ((F α)ᴴ) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.kronecker (fibonacciPeircePlusComplex * (F α)ᴴ)
          (Matrix.single r s 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul fibonacciPeircePlusComplex ((F α)ᴴ)
        (Matrix.single r s (1 : ℂ)) (1 : Matrix (Fin 2) (Fin 2) ℂ)).symm
  have hmul2 :
      Matrix.kronecker (fibonacciPeircePlusComplex * (F α)ᴴ)
          (Matrix.single r s 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          Matrix.kronecker (F β) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.kronecker ((fibonacciPeircePlusComplex * (F α)ᴴ) * F β)
          ((Matrix.single r s 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (fibonacciPeircePlusComplex * (F α)ᴴ) (F β)
        (Matrix.single r s (1 : ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)).symm
  have hmul3 :
      Matrix.kronecker ((fibonacciPeircePlusComplex * (F α)ᴴ) * F β)
          ((Matrix.single r s 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          Matrix.kronecker fibonacciPeircePlusComplex (Matrix.single t u 1) =
        Matrix.kronecker (((fibonacciPeircePlusComplex * (F α)ᴴ) * F β) *
            fibonacciPeircePlusComplex)
          (((Matrix.single r s 1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Matrix.single t u 1) := by
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul ((fibonacciPeircePlusComplex * (F α)ᴴ) * F β)
        fibonacciPeircePlusComplex
        ((Matrix.single r s (1 : ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (Matrix.single t u (1 : ℂ))).symm
  rw [hmul1, hmul2, hmul3]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rw [show fibonacciPeircePlusComplex * (F α)ᴴ * F β *
      fibonacciPeircePlusComplex =
      fibonacciPeircePlusComplex * ((F α)ᴴ * F β) *
        fibonacciPeircePlusComplex by noncomm_ring]
  rw [P_mul_A_mul_P, hsingle]
  by_cases hst : s = t
  · simp [hst, Matrix.smul_kronecker]
  · simp [hst, Matrix.kronecker_zero]

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

def cuntzLogicalMatrixUnit (r s : Fin 2) : A :=
  cuntzWordTwoCornerMap S (logicalMatrixUnit r s)

def cuntzFirstFactorError {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) (α : ι) : A :=
  cuntzWordTwoCornerMap S (firstFactorError F α)

theorem cuntzLogicalMatrixUnit_error_compression
    {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (r s t u : Fin 2)
    (α β : ι) :
    cuntzLogicalMatrixUnit S r s *
        star (cuntzFirstFactorError S F α) *
        cuntzFirstFactorError S F β *
        cuntzLogicalMatrixUnit S t u =
      if s = t then
        (((F α)ᴴ * F β * fibonacciPeircePlusComplex).trace) •
          cuntzLogicalMatrixUnit S r u
      else 0 := by
  have h := logicalMatrixUnit_error_compression F r s t u α β
  have hmap := congrArg (cuntzWordTwoCornerMap S) h
  unfold cuntzLogicalMatrixUnit cuntzFirstFactorError
  by_cases hst : s = t
  · simp only [hst, if_true] at hmap ⊢
    rw [cuntzWordTwoCornerMap_smul] at hmap
    simpa only [cuntzWordTwoCornerMap_mul,
      cuntzWordTwoCornerMap_conjTranspose, cuntzWordTwoCornerMap_smul,
      Algebra.smul_def, map_mul] using hmap
  · simp only [hst, if_false] at hmap ⊢
    simpa only [cuntzWordTwoCornerMap_mul,
      cuntzWordTwoCornerMap_conjTranspose, cuntzWordTwoCornerMap_zero] using hmap

end CuntzPeirceLogicalCorner
