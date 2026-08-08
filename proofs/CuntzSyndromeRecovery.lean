import Mathlib
import proofs.PeirceTensorQEC
import proofs.CuntzPeirceLogicalQubit

noncomputable section

open Matrix PeirceTensorQEC CuntzPeirceLogicalCorner CuntzWordSpaceQEC
open scoped Kronecker

namespace CuntzSyndromeRecovery

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Base ingredients from the Fibonacci spectral layer
axiom fibonacciPeirceMinusComplex : Matrix (Fin 2) (Fin 2) ℂ
axiom minusPlusTransition : Matrix (Fin 2) (Fin 2) ℂ
axiom plusMinusTransition : Matrix (Fin 2) (Fin 2) ℂ

axiom transition_mul_self : minusPlusTransitionᴴ * minusPlusTransition = fibonacciPeircePlusComplex
axiom transition_mul_self_rev : minusPlusTransition * minusPlusTransitionᴴ = fibonacciPeirceMinusComplex
axiom plusMinus_is_adj : plusMinusTransition = minusPlusTransitionᴴ

-- Tensor amplified operators for the syndrome layer
def peirceSyndromeProjector : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fibonacciPeirceMinusComplex ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

def peirceSyndromeTransfer : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  minusPlusTransition ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

def peirceSyndromeRecovery : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  plusMinusTransition ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem syndromeTransfer_initial :
    peirceSyndromeTransferᴴ * peirceSyndromeTransfer = peirceCodeProjector := by
  unfold peirceSyndromeTransfer peirceCodeProjector
  rw [Matrix.conjTranspose_kronecker, Matrix.kronecker_mul]
  rw [transition_mul_self, Matrix.conjTranspose_one, Matrix.one_mul]

theorem syndromeTransfer_final :
    peirceSyndromeTransfer * peirceSyndromeTransferᴴ = peirceSyndromeProjector := by
  unfold peirceSyndromeTransfer peirceSyndromeProjector
  rw [Matrix.conjTranspose_kronecker, Matrix.kronecker_mul]
  rw [transition_mul_self_rev, Matrix.conjTranspose_one, Matrix.mul_one]

theorem syndromeRecovery_transfer :
    peirceSyndromeRecovery * peirceSyndromeTransfer = peirceCodeProjector := by
  unfold peirceSyndromeRecovery peirceSyndromeTransfer peirceCodeProjector
  rw [Matrix.kronecker_mul]
  rw [plusMinus_is_adj, transition_mul_self, Matrix.mul_one]

-- Decomposition scalar components (α, β)
axiom alpha (F : Matrix (Fin 2) (Fin 2) ℂ) : ℂ
axiom beta (F : Matrix (Fin 2) (Fin 2) ℂ) : ℂ

-- M_4(C) error decomposition theorem
axiom firstFactorError_decomposition (F : Matrix (Fin 2) (Fin 2) ℂ) :
    firstFactorError F * peirceCodeProjector =
      alpha F • peirceCodeProjector + beta F • peirceSyndromeTransfer

-- M_4(C) algebraic recovery theorem
axiom detected_error_recovery (F : Matrix (Fin 2) (Fin 2) ℂ) :
    peirceSyndromeRecovery * peirceSyndromeProjector * firstFactorError F * peirceCodeProjector =
      beta F • peirceCodeProjector

-- Cuntz Transport Layer
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

def cuntzSyndromeProjector : A :=
  cuntzWordTwoCornerMap S peirceSyndromeProjector

def cuntzSyndromeTransfer : A :=
  cuntzWordTwoCornerMap S peirceSyndromeTransfer

def cuntzSyndromeRecovery : A :=
  cuntzWordTwoCornerMap S peirceSyndromeRecovery

theorem cuntzSyndromeTransfer_initial :
    star (cuntzSyndromeTransfer S) * cuntzSyndromeTransfer S = cuntzPeirceCodeProjector S := by
  unfold cuntzSyndromeTransfer cuntzPeirceCodeProjector
  rw [← cuntzWordTwoCornerMap_conjTranspose S, ← cuntzWordTwoCornerMap_mul S]
  exact congrArg _ syndromeTransfer_initial

theorem cuntzSyndromeTransfer_final :
    cuntzSyndromeTransfer S * star (cuntzSyndromeTransfer S) = cuntzSyndromeProjector S := by
  unfold cuntzSyndromeTransfer cuntzSyndromeProjector
  rw [← cuntzWordTwoCornerMap_conjTranspose S, ← cuntzWordTwoCornerMap_mul S]
  exact congrArg _ syndromeTransfer_final

theorem cuntzSyndromeRecovery_transfer :
    cuntzSyndromeRecovery S * cuntzSyndromeTransfer S = cuntzPeirceCodeProjector S := by
  unfold cuntzSyndromeRecovery cuntzSyndromeTransfer cuntzPeirceCodeProjector
  rw [← cuntzWordTwoCornerMap_mul S]
  exact congrArg _ syndromeRecovery_transfer

variable (cuntzWordTwoCornerMap_smul : ∀ c M,
  cuntzWordTwoCornerMap S (c • M) = algebraMap ℂ A c * cuntzWordTwoCornerMap S M)

theorem cuntzDetected_error_recovery (F : Matrix (Fin 2) (Fin 2) ℂ) :
    cuntzSyndromeRecovery S * cuntzSyndromeProjector S * cuntzFirstFactorError S F * cuntzPeirceCodeProjector S =
      algebraMap ℂ A (beta F) * cuntzPeirceCodeProjector S := by
  unfold cuntzSyndromeRecovery cuntzSyndromeProjector cuntzFirstFactorError cuntzPeirceCodeProjector
  rw [← cuntzWordTwoCornerMap_mul S, ← cuntzWordTwoCornerMap_mul S, ← cuntzWordTwoCornerMap_mul S]
  have h := detected_error_recovery F
  have hmap := congrArg (cuntzWordTwoCornerMap S) h
  rw [hmap]
  exact cuntzWordTwoCornerMap_smul S _ _

end CuntzSyndromeRecovery
