import Mathlib
import proofs.CuntzZornIntegration
import proofs.FibonacciPeirceProjectors

noncomputable section

open Matrix Real CuntzZornIntegration FibonacciPeirceProjectors

namespace KnillLaflammeQEC

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- 1. Abstract Knill-Laflamme Condition -/

abbrev ErrorFamily (E : Type*) [Fintype E] (n : Type*) [Fintype n] := E → Matrix n n ℝ

/-- 
The real Knill-Laflamme Quantum Error Correction condition:
P_C E_a^T E_b P_C = λ_{ab} P_C
-/
def satisfiesKnillLaflamme
    (P_C : Matrix n n ℝ)
    (errors : ErrorFamily E n)
    (lambda : Matrix E E ℝ) : Prop :=
  ∀ a b : E, P_C * (errors a)ᵀ * (errors b) * P_C = (lambda a b) • P_C

/-- 2. Fibonacci Peirce Projector as the Code Space -/

def P_C_Fibonacci : Matrix (Fin 2) (Fin 2) ℝ :=
  fibonacciPeircePlus

/-- 3. Transpose Symmetries of Peirce Projectors -/

theorem peirceGoldenProjector_symm : P_C_Fibonacciᵀ = P_C_Fibonacci :=
  fibonacciPeircePlus_selfAdjoint

theorem peirceGoldenProjectorMinus_symm : fibonacciPeirceMinusᵀ = fibonacciPeirceMinus :=
  fibonacciPeirceMinus_selfAdjoint

/-- 4. Orthogonal Noise Model (Tangential Displacement) -/

-- A simple error model where the only error is a displacement along the orthogonal projection
def orthogonalError (e : Fin 1) : Matrix (Fin 2) (Fin 2) ℝ :=
  fibonacciPeirceMinus

def zeroLambda (a b : Fin 1) : ℝ := 0

/-- 5. Knill-Laflamme Verification -/

theorem fibonacci_satisfies_KL_orthogonal :
    satisfiesKnillLaflamme P_C_Fibonacci orthogonalError zeroLambda := by
  intro a b
  dsimp [satisfiesKnillLaflamme, P_C_Fibonacci, orthogonalError, zeroLambda]
  simp only [zero_smul]
  
  rw [peirceGoldenProjectorMinus_symm]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  
  have h_ortho : fibonacciPeircePlus * fibonacciPeirceMinus = 0 := fibonacciPeirce_orthogonal
  
  calc
    fibonacciPeircePlus * (fibonacciPeirceMinus * (fibonacciPeirceMinus * fibonacciPeircePlus))
      = (fibonacciPeircePlus * fibonacciPeirceMinus) * (fibonacciPeirceMinus * fibonacciPeircePlus) := by rw [← Matrix.mul_assoc]
    _ = 0 * (fibonacciPeirceMinus * fibonacciPeircePlus) := by rw [h_ortho]
    _ = 0 := by simp

-- For CuntzCornerQEC.lean compatibility
def fibonacciErrors (a : Fin 1) : Matrix (Fin 2) (Fin 2) ℝ := orthogonalError a
theorem fibonacci_satisfies_KL : satisfiesKnillLaflamme P_C_Fibonacci fibonacciErrors zeroLambda := fibonacci_satisfies_KL_orthogonal

end KnillLaflammeQEC
