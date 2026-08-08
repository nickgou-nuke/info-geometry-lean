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
  fibonacciPeircePlusComplex ⊗ₖ Matrix.stdBasisMatrix a b (1 : ℂ)

-- Assume this is proven in the lower layer
axiom logicalMatrixUnit_error_compression
    {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (r s t u : Fin 2)
    (α β : ι) :
    logicalMatrixUnit r s *
        (firstFactorError F α)ᴴ *
        firstFactorError F β *
        logicalMatrixUnit t u =
      if s = t then
        (dotProduct (star n_plus_complex) (((F α)ᴴ * F β) *ᵥ n_plus_complex)) •
          logicalMatrixUnit r u
      else 0

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

def cuntzLogicalMatrixUnit (r s : Fin 2) : A :=
  cuntzWordTwoCornerMap S (logicalMatrixUnit r s)

def cuntzFirstFactorError {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) (α : ι) : A :=
  cuntzWordTwoCornerMap S (firstFactorError F α)

variable (cuntzWordTwoCornerMap_mul : ∀ M N : Word2Matrix,
  cuntzWordTwoCornerMap S (M * N) = cuntzWordTwoCornerMap S M * cuntzWordTwoCornerMap S N)
variable (cuntzWordTwoCornerMap_star : ∀ M : Word2Matrix,
  cuntzWordTwoCornerMap S Mᴴ = star (cuntzWordTwoCornerMap S M))
variable (cuntzWordTwoCornerMap_smul : ∀ c M,
  cuntzWordTwoCornerMap S (c • M) = c • cuntzWordTwoCornerMap S M)
variable (cuntzWordTwoCornerMap_zero : cuntzWordTwoCornerMap S 0 = 0)

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
        (dotProduct (star n_plus_complex) (((F α)ᴴ * F β) *ᵥ n_plus_complex)) •
          cuntzLogicalMatrixUnit S r u
      else 0 := by
  have h := logicalMatrixUnit_error_compression F r s t u α β
  have hmap := congrArg (cuntzWordTwoCornerMap S) h
  unfold cuntzLogicalMatrixUnit cuntzFirstFactorError
  rw [← cuntzWordTwoCornerMap_mul, ← cuntzWordTwoCornerMap_mul, ← cuntzWordTwoCornerMap_mul]
  rw [← cuntzWordTwoCornerMap_star]
  by_cases hst : s = t
  · simp only [hst, if_true] at hmap ⊢
    rw [hmap]
    exact cuntzWordTwoCornerMap_smul S _ _
  · simp only [hst, if_false] at hmap ⊢
    rw [hmap]
    exact cuntzWordTwoCornerMap_zero S

end CuntzPeirceLogicalCorner
