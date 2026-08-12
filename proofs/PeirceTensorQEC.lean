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
    have h := congr_fun (congr_fun fibonacciPeircePlus_selfAdjoint i) j
    simpa [Matrix.transpose_apply] using h
  rw [h_symm]
  exact Complex.conj_ofReal _

theorem fibonacciPeircePlusComplex_idempotent :
    fibonacciPeircePlusComplex * fibonacciPeircePlusComplex = fibonacciPeircePlusComplex := by
  ext i j
  dsimp [fibonacciPeircePlusComplex, Matrix.mul_apply]
  simp only [Fin.sum_univ_two]
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
  fin_cases i <;> fin_cases j
  all_goals simp [fibonacciPeircePlusComplex, fibonacciPeircePlus, fibonacciMatrixReal,
    tau, Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
    Fin.sum_univ_two]
  all_goals
    have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.sqrt 5 ≠ 0 by positivity)
    have h : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      exact_mod_cast sqrt5_sq
    field_simp [hs]
    ring_nf
    rw [h]
    ring

-- By definition, it satisfies the rank-one Knill-Laflamme condition (Degenerate Code)
theorem fibonacciPeircePlus_knillLaflamme {ι : Type*} (E : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    FiniteMatrixKnillLaflamme.SatisfiesKnillLaflamme fibonacciPeircePlusComplex E := by
  use fun a b => ((E a)ᴴ * (E b) * fibonacciPeircePlusComplex).trace
  intro a b
  simpa [Matrix.mul_assoc] using P_mul_A_mul_P ((E a)ᴴ * (E b))

/-- 2. Tensor Amplification: The True Non-Trivial Code -/
-- We amplify the state space to H_phys = C^2 \otimes C^2 and define P_C = P_+ \otimes I_2
def peirceCodeProjector : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker fibonacciPeircePlusComplex (1 : Matrix (Fin 2) (Fin 2) ℂ)

-- Errors that only act on the first factor: E_a = F_a \otimes I_2
def firstFactorError {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) (a : ι) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (F a) (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem peirceCodeProjector_selfAdjoint :
    peirceCodeProjectorᴴ = peirceCodeProjector := by
  dsimp [peirceCodeProjector]
  rw [Matrix.conjTranspose_kronecker,
    fibonacciPeircePlusComplex_selfAdjoint, Matrix.conjTranspose_one]

theorem peirceCodeProjector_idempotent :
    peirceCodeProjector * peirceCodeProjector = peirceCodeProjector := by
  dsimp [peirceCodeProjector]
  rw [← Matrix.mul_kronecker_mul,
    fibonacciPeircePlusComplex_idempotent, Matrix.mul_one]

-- This is a rank-2 code projector, capable of carrying 1 logical qubit.
theorem peirceCodeProjector_trace_two :
    Matrix.trace peirceCodeProjector = 2 := by
  dsimp [peirceCodeProjector]
  rw [Matrix.trace_kronecker]
  have h_trace : Matrix.trace fibonacciPeircePlusComplex = 1 := by
    dsimp [fibonacciPeircePlusComplex, fibonacciPeircePlus, fibonacciMatrixReal,
      Matrix.trace, tau, phi]
    norm_num
    have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.sqrt 5 ≠ 0 by positivity)
    have h : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      exact_mod_cast sqrt5_sq
    field_simp [hs]
    ring_nf
  rw [h_trace]
  have h_trace_one : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
    simp [Matrix.trace]
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
  calc
    _ = Matrix.kronecker
        (fibonacciPeircePlusComplex * (F a)ᴴ * F b * fibonacciPeircePlusComplex)
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 * 1 * 1) := by
      simp only [Matrix.mul_one]
      rw [Matrix.conjTranspose_kronecker]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul]
      simp [Matrix.conjTranspose_one]
    _ = _ := by rw [h_lambda a b]; simp [Matrix.smul_kronecker]

end PeirceTensorQEC
