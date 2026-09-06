import Mathlib
import proofs.PeirceTensorQEC
import proofs.CuntzPeirceLogicalQubit

noncomputable section

open Matrix PeirceTensorQEC CuntzPeirceLogicalCorner CuntzWordSpaceQEC
open scoped Kronecker

namespace CuntzSyndromeRecovery

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev WordTwoMatrix := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The real quarter-turn used to identify the two complementary Fibonacci
Peirce lines. -/
def quarterTurn : QubitMatrix := !![0, -1; 1, 0]

/-- The complementary Peirce projector. -/
def fibonacciPeirceMinusComplex : QubitMatrix :=
  1 - fibonacciPeircePlusComplex

/-- Partial isometry from the positive Peirce line to its orthogonal
complement. -/
def minusPlusTransition : QubitMatrix :=
  quarterTurn * fibonacciPeircePlusComplex

/-- Reverse transition. -/
def plusMinusTransition : QubitMatrix :=
  minusPlusTransitionᴴ

private theorem quarterTurn_star_mul :
    quarterTurnᴴ * quarterTurn = (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterTurn, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem transition_right_support :
    minusPlusTransition * fibonacciPeircePlusComplex = minusPlusTransition := by
  rw [minusPlusTransition, Matrix.mul_assoc,
    fibonacciPeircePlusComplex_idempotent]

/-- The transition has initial projection `P₊`. -/
theorem transition_mul_self :
    minusPlusTransitionᴴ * minusPlusTransition = fibonacciPeircePlusComplex := by
  calc
    minusPlusTransitionᴴ * minusPlusTransition =
        fibonacciPeircePlusComplexᴴ * quarterTurnᴴ *
          (quarterTurn * fibonacciPeircePlusComplex) := by
      rw [minusPlusTransition, Matrix.conjTranspose_mul]
    _ = fibonacciPeircePlusComplex * (quarterTurnᴴ * quarterTurn) *
          fibonacciPeircePlusComplex := by
      rw [fibonacciPeircePlusComplex_selfAdjoint]
      noncomm_ring
    _ = fibonacciPeircePlusComplex * 1 * fibonacciPeircePlusComplex := by
      rw [quarterTurn_star_mul]
    _ = fibonacciPeircePlusComplex := by
      simp [fibonacciPeircePlusComplex_idempotent]

/-- The transition has final projection `P₋`. -/
theorem transition_mul_self_rev :
    minusPlusTransition * minusPlusTransitionᴴ = fibonacciPeirceMinusComplex := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [minusPlusTransition, quarterTurn, fibonacciPeirceMinusComplex,
      fibonacciPeircePlusComplex, FibonacciPeirceProjectors.fibonacciPeircePlus,
      FibonacciPeirceProjectors.fibonacciMatrixReal,
      FibonacciPeirceProjectors.tau, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two]
  all_goals
    have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.sqrt 5 ≠ 0 by positivity)
    have hs2 : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      exact_mod_cast FibonacciPeirceProjectors.sqrt5_sq
    field_simp [hs] <;>
      ring_nf <;>
      (try rw [hs2]) <;>
      ring

@[simp] theorem plusMinus_is_adj :
    plusMinusTransition = minusPlusTransitionᴴ := rfl

private theorem peirce_projector_sum :
    fibonacciPeircePlusComplex + fibonacciPeirceMinusComplex = 1 := by
  simp [fibonacciPeirceMinusComplex]

/-- Tensor-amplified syndrome projector. -/
def peirceSyndromeProjector : WordTwoMatrix :=
  fibonacciPeirceMinusComplex ⊗ₖ (1 : QubitMatrix)

/-- Tensor-amplified syndrome transfer. -/
def peirceSyndromeTransfer : WordTwoMatrix :=
  minusPlusTransition ⊗ₖ (1 : QubitMatrix)

/-- Tensor-amplified recovery map. -/
def peirceSyndromeRecovery : WordTwoMatrix :=
  plusMinusTransition ⊗ₖ (1 : QubitMatrix)

/-- A single first-factor error on the amplified two-qubit carrier. -/
def firstFactorMatrixError (F : QubitMatrix) : WordTwoMatrix :=
  F ⊗ₖ (1 : QubitMatrix)

theorem syndromeTransfer_initial :
    peirceSyndromeTransferᴴ * peirceSyndromeTransfer = peirceCodeProjector := by
  unfold peirceSyndromeTransfer peirceCodeProjector
  rw [Matrix.conjTranspose_kronecker]
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp [transition_mul_self]

theorem syndromeTransfer_final :
    peirceSyndromeTransfer * peirceSyndromeTransferᴴ = peirceSyndromeProjector := by
  unfold peirceSyndromeTransfer peirceSyndromeProjector
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp [transition_mul_self_rev]

theorem syndromeRecovery_transfer :
    peirceSyndromeRecovery * peirceSyndromeTransfer = peirceCodeProjector := by
  unfold peirceSyndromeRecovery peirceSyndromeTransfer peirceCodeProjector
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp [transition_mul_self]

/-- Positive-line coefficient of an arbitrary first-factor error. -/
def alpha (F : QubitMatrix) : ℂ :=
  (F * fibonacciPeircePlusComplex).trace

/-- Syndrome-line coefficient of an arbitrary first-factor error. -/
def beta (F : QubitMatrix) : ℂ :=
  (minusPlusTransitionᴴ * F * fibonacciPeircePlusComplex).trace

private theorem peirceMinus_error_peircePlus (F : QubitMatrix) :
    fibonacciPeirceMinusComplex * F * fibonacciPeircePlusComplex =
      beta F • minusPlusTransition := by
  have hcross := P_mul_A_mul_P (minusPlusTransitionᴴ * F)
  have hsupport := transition_right_support
  calc
    fibonacciPeirceMinusComplex * F * fibonacciPeircePlusComplex =
        (minusPlusTransition * minusPlusTransitionᴴ) * F *
          fibonacciPeircePlusComplex := by rw [transition_mul_self_rev]
    _ = minusPlusTransition * (minusPlusTransitionᴴ * F) *
          fibonacciPeircePlusComplex := by
      noncomm_ring
    _ = (minusPlusTransition * fibonacciPeircePlusComplex) *
          (minusPlusTransitionᴴ * F) * fibonacciPeircePlusComplex := by
      rw [hsupport]
    _ = minusPlusTransition *
        (fibonacciPeircePlusComplex * (minusPlusTransitionᴴ * F) *
          fibonacciPeircePlusComplex) := by
      noncomm_ring
    _ = minusPlusTransition *
        (beta F • fibonacciPeircePlusComplex) := by
      rw [hcross]
      rfl
    _ = beta F • minusPlusTransition := by
      rw [Matrix.mul_smul, transition_right_support]

private theorem firstFactor_base_decomposition (F : QubitMatrix) :
    F * fibonacciPeircePlusComplex =
      alpha F • fibonacciPeircePlusComplex + beta F • minusPlusTransition := by
  have hplus := P_mul_A_mul_P F
  calc
    F * fibonacciPeircePlusComplex =
        (fibonacciPeircePlusComplex + fibonacciPeirceMinusComplex) * F *
          fibonacciPeircePlusComplex := by
      rw [peirce_projector_sum]
      simp
    _ = fibonacciPeircePlusComplex * F * fibonacciPeircePlusComplex +
        fibonacciPeirceMinusComplex * F * fibonacciPeircePlusComplex := by
      noncomm_ring
    _ = alpha F • fibonacciPeircePlusComplex +
        beta F • minusPlusTransition := by
      rw [hplus, peirceMinus_error_peircePlus]
      rfl

/-- Every first-factor error sends the code line into the direct sum of the
code and syndrome lines. -/
theorem firstFactorError_decomposition (F : QubitMatrix) :
    firstFactorMatrixError F * peirceCodeProjector =
      alpha F • peirceCodeProjector + beta F • peirceSyndromeTransfer := by
  unfold firstFactorMatrixError peirceCodeProjector peirceSyndromeTransfer
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one,
    firstFactor_base_decomposition, Matrix.add_kronecker,
    Matrix.smul_kronecker, Matrix.smul_kronecker]

private theorem base_detected_error_recovery (F : QubitMatrix) :
    plusMinusTransition * fibonacciPeirceMinusComplex * F *
        fibonacciPeircePlusComplex =
      beta F • fibonacciPeircePlusComplex := by
  rw [show plusMinusTransition * fibonacciPeirceMinusComplex * F *
      fibonacciPeircePlusComplex =
      plusMinusTransition *
        (fibonacciPeirceMinusComplex * F * fibonacciPeircePlusComplex) by
        noncomm_ring]
  rw [peirceMinus_error_peircePlus]
  simp [plusMinusTransition, transition_mul_self]

/-- The reverse partial isometry recovers the detected syndrome component. -/
theorem detected_error_recovery (F : QubitMatrix) :
    peirceSyndromeRecovery * peirceSyndromeProjector *
        firstFactorMatrixError F * peirceCodeProjector =
      beta F • peirceCodeProjector := by
  unfold peirceSyndromeRecovery peirceSyndromeProjector
  unfold firstFactorMatrixError peirceCodeProjector
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  rw [base_detected_error_recovery, Matrix.smul_kronecker]

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [CuntzO2 (S 0) (S 1)]

def cuntzSyndromeProjector : A :=
  cuntzWordTwoCornerMap S peirceSyndromeProjector

def cuntzSyndromeTransfer : A :=
  cuntzWordTwoCornerMap S peirceSyndromeTransfer

def cuntzSyndromeRecovery : A :=
  cuntzWordTwoCornerMap S peirceSyndromeRecovery

def cuntzFirstFactorMatrixError (F : QubitMatrix) : A :=
  cuntzWordTwoCornerMap S (firstFactorMatrixError F)

theorem cuntzSyndromeTransfer_initial :
    star (cuntzSyndromeTransfer S) * cuntzSyndromeTransfer S =
      cuntzPeirceCodeProjector S := by
  simpa only [cuntzSyndromeTransfer, cuntzPeirceCodeProjector,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_mul,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_conjTranspose] using
    congrArg (cuntzWordTwoCornerMap S) syndromeTransfer_initial

theorem cuntzSyndromeTransfer_final :
    cuntzSyndromeTransfer S * star (cuntzSyndromeTransfer S) =
      cuntzSyndromeProjector S := by
  simpa only [cuntzSyndromeTransfer, cuntzSyndromeProjector,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_mul,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_conjTranspose] using
    congrArg (cuntzWordTwoCornerMap S) syndromeTransfer_final

theorem cuntzSyndromeRecovery_transfer :
    cuntzSyndromeRecovery S * cuntzSyndromeTransfer S =
      cuntzPeirceCodeProjector S := by
  simpa only [cuntzSyndromeRecovery, cuntzSyndromeTransfer,
    cuntzPeirceCodeProjector,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_mul] using
    congrArg (cuntzWordTwoCornerMap S) syndromeRecovery_transfer

theorem cuntzDetected_error_recovery (F : QubitMatrix) :
    cuntzSyndromeRecovery S * cuntzSyndromeProjector S *
        cuntzFirstFactorMatrixError S F * cuntzPeirceCodeProjector S =
      algebraMap ℂ A (beta F) * cuntzPeirceCodeProjector S := by
  simpa only [cuntzSyndromeRecovery, cuntzSyndromeProjector,
    cuntzFirstFactorMatrixError, cuntzPeirceCodeProjector,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_mul,
    CuntzWordSpaceQEC.cuntzWordTwoCornerMap_smul] using
    congrArg (cuntzWordTwoCornerMap S) (detected_error_recovery F)

end CuntzSyndromeRecovery
