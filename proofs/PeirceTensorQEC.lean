import Mathlib
import proofs.FiniteMatrixKnillLaflamme
import proofs.FibonacciPeirceProjectors

noncomputable section

open Matrix Complex FibonacciPeirceProjectors

namespace PeirceTensorQEC

/-- 1. Complexified Peirce Projector -/
def fibonacciPeircePlusComplex : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (fibonacciPeircePlus i j : ℂ)

theorem fibonacciPeircePlusComplex_selfAdjoint :
    fibonacciPeircePlusComplexᴴ = fibonacciPeircePlusComplex := by
  ext i j
  dsimp [fibonacciPeircePlusComplex, Matrix.conjTranspose_apply]
  have h_symm : fibonacciPeircePlus j i = fibonacciPeircePlus i j := by
    have h := congr_fun (congr_fun fibonacciPeircePlus_selfAdjoint j) i
    exact h
  rw [h_symm]
  exact Complex.conj_ofReal _

theorem fibonacciPeircePlusComplex_idempotent :
    fibonacciPeircePlusComplex * fibonacciPeircePlusComplex = fibonacciPeircePlusComplex := by
  ext i j
  dsimp [fibonacciPeircePlusComplex, Matrix.mul_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  push_cast
  have h := congr_fun (congr_fun fibonacciPeircePlus_idempotent i) j
  dsimp [Matrix.mul_apply] at h
  rw [Fin.sum_univ_two] at h
  exact_mod_cast h

theorem fibonacciPeircePlusComplex_isOrthogonalProjection :
    FiniteMatrixKnillLaflamme.IsOrthogonalProjection fibonacciPeircePlusComplex :=
  ⟨fibonacciPeircePlusComplex_selfAdjoint, fibonacciPeircePlusComplex_idempotent⟩

lemma P_mul_A_mul_P (A : Matrix (Fin 2) (Fin 2) ℂ) :
    fibonacciPeircePlusComplex * A * fibonacciPeircePlusComplex = (A * fibonacciPeircePlusComplex).trace • fibonacciPeircePlusComplex := by
  ext i j
  dsimp [fibonacciPeircePlusComplex, fibonacciPeircePlus, fibonacciMatrixReal, phi, tau, Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> {
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    push_cast
    have h : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      push_cast
      exact_mod_cast sqrt5_sq
    nlinarith [h]
  }

-- By definition, it satisfies the rank-one Knill-Laflamme condition (Degenerate Code)
theorem fibonacciPeircePlus_knillLaflamme {ι : Type*} (E : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    FiniteMatrixKnillLaflamme.SatisfiesKnillLaflamme fibonacciPeircePlusComplex E := by
  use fun a b => ((E a)ᴴ * (E b) * fibonacciPeircePlusComplex).trace
  intro a b
  exact P_mul_A_mul_P ((E a)ᴴ * (E b))

/-- 2. Tensor Amplification: The True Non-Trivial Code -/
-- We amplify the state space to H_phys = C^2 \otimes C^2 and define P_C = P_+ \otimes I_2
def peirceCodeProjector : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fibonacciPeircePlusComplex ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

-- Errors that only act on the first factor: E_a = F_a \otimes I_2
def firstFactorError {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) (a : ι) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  F a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem peirceCodeProjector_selfAdjoint :
    peirceCodeProjectorᴴ = peirceCodeProjector := by
  dsimp [peirceCodeProjector]
  rw [Matrix.kronecker_conjTranspose]
  rw [fibonacciPeircePlusComplex_selfAdjoint]
  rw [Matrix.conjTranspose_one]

theorem peirceCodeProjector_idempotent :
    peirceCodeProjector * peirceCodeProjector = peirceCodeProjector := by
  dsimp [peirceCodeProjector]
  rw [Matrix.mul_kronecker]
  rw [fibonacciPeircePlusComplex_idempotent]
  rw [Matrix.mul_one]

-- This is a rank-2 code projector, capable of carrying 1 logical qubit.
theorem peirceCodeProjector_trace_two :
    Matrix.trace peirceCodeProjector = 2 := by
  dsimp [peirceCodeProjector]
  rw [Matrix.trace_kronecker]
  have h_trace : Matrix.trace fibonacciPeircePlusComplex = 1 := by
    dsimp [fibonacciPeircePlusComplex, fibonacciPeircePlus, fibonacciMatrixReal, Matrix.trace, tau, phi]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    push_cast
    have h : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by push_cast; exact_mod_cast sqrt5_sq
    nlinarith [h]
  rw [h_trace]
  have h_trace_one : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
    dsimp [Matrix.trace, Matrix.one_apply]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num
  rw [h_trace_one]
  ring

/-- 3. Knill-Laflamme for the Tensor Code -/
-- This shows the amplified code corrects arbitrary errors on the first qubit factor
theorem peirceTensor_knillLaflamme {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    FiniteMatrixKnillLaflamme.SatisfiesKnillLaflamme peirceCodeProjector (firstFactorError F) := by
  obtain ⟨lambda, h_lambda⟩ := fibonacciPeircePlus_knillLaflamme F
  use lambda
  intro a b
  dsimp [peirceCodeProjector, firstFactorError]
  rw [Matrix.kronecker_conjTranspose]
  rw [Matrix.conjTranspose_one]
  rw [Matrix.mul_kronecker, Matrix.mul_kronecker]
  rw [Matrix.mul_one, Matrix.mul_one]
  rw [h_lambda a b]
  rw [Matrix.smul_kronecker]

end PeirceTensorQEC
