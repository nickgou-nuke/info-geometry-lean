import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.SpectralToken

/-!
# Directed operator doubling

This is the finite matrix realization of a forward/reverse two-lane carrier.
It mirrors the repository's symmetric/antisymmetric correlation convention and
reuses the existing LLM `SpectralToken` only as a neutral primal/dual carrier.
No physical Majorana identification is asserted.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix

variable {n d : ℕ}

/-- Reciprocal part of a directed finite operator. -/
def symmetricPart (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (K + K.transpose)

/-- Oriented part of a directed finite operator. -/
def antisymmetricPart (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (K - K.transpose)

theorem symmetricPart_add_antisymmetricPart
    (K : Matrix (Fin n) (Fin n) ℝ) :
    symmetricPart K + antisymmetricPart K = K := by
  ext i j
  simp [symmetricPart, antisymmetricPart]
  ring

theorem symmetricPart_transpose
    (K : Matrix (Fin n) (Fin n) ℝ) :
    (symmetricPart K).transpose = symmetricPart K := by
  ext i j
  simp [symmetricPart, add_comm]
  rw [mul_add]

theorem antisymmetricPart_transpose
    (K : Matrix (Fin n) (Fin n) ℝ) :
    (antisymmetricPart K).transpose = -antisymmetricPart K := by
  ext i j
  simp [antisymmetricPart]
  ring

/-- Row Gram operator of finite feature vectors. -/
def gramOperator (Z : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Z * Z.transpose

theorem gramOperator_transpose
    (Z : Matrix (Fin n) (Fin d) ℝ) :
    (gramOperator Z).transpose = gramOperator Z := by
  simp [gramOperator, Matrix.transpose_mul]

/-- A genuine real Gram operator has no oriented/antisymmetric component. -/
theorem antisymmetricPart_gramOperator_eq_zero
    (Z : Matrix (Fin n) (Fin d) ℝ) :
    antisymmetricPart (gramOperator Z) = 0 := by
  ext i j
  simp [antisymmetricPart, gramOperator_transpose]

/-- Forward/reverse labels for the doubled finite carrier. -/
abbrev DoubledIndex (n : ℕ) := Sum (Fin n) (Fin n)

/-- Off-diagonal doubling `[[0,K],[Kᵀ,0]]`. -/
def doubledOperator (K : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ := fun i j =>
  match i, j with
  | Sum.inl a, Sum.inr b => K a b
  | Sum.inr a, Sum.inl b => K b a
  | _, _ => 0

theorem doubledOperator_transpose
    (K : Matrix (Fin n) (Fin n) ℝ) :
    (doubledOperator K).transpose = doubledOperator K := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Diagonal sign of the two-lane grading. -/
def doubledSign : DoubledIndex n → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

@[simp] theorem doubledSign_sq (i : DoubledIndex n) :
    doubledSign i * doubledSign i = 1 := by
  cases i <;> simp [doubledSign]

/-- Full matrix grading `Γ = diag(+I,-I)`. -/
def gradingMatrix (n : ℕ) : Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  Matrix.diagonal doubledSign

/-- The grading is an involution. -/
theorem gradingMatrix_sq (n : ℕ) :
    gradingMatrix n * gradingMatrix n = 1 := by
  classical
  rw [gradingMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [doubledSign_sq]
  · simp [h]

/-- Entrywise left action by the grading. -/
def gradeLeft (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  fun i j => doubledSign i * A i j

/-- Entrywise right action by the grading. -/
def gradeRight (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  fun i j => A i j * doubledSign j

/-- Matrix multiplication by `Γ` agrees with the left grading action. -/
theorem gradingMatrix_mul_eq_gradeLeft
    (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    gradingMatrix n * A = gradeLeft A := by
  ext i j
  rw [gradingMatrix, Matrix.diagonal_mul]
  rfl

/-- Matrix multiplication by `Γ` agrees with the right grading action. -/
theorem mul_gradingMatrix_eq_gradeRight
    (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    A * gradingMatrix n = gradeRight A := by
  ext i j
  rw [gradingMatrix, Matrix.mul_diagonal]
  rfl

/-- The off-diagonal doubling reverses the two-lane grading. -/
theorem doubledOperator_grade_reversing
    (K : Matrix (Fin n) (Fin n) ℝ) :
    gradeLeft (doubledOperator K) = -gradeRight (doubledOperator K) := by
  ext i j
  cases i <;> cases j <;>
    simp [gradeLeft, gradeRight, doubledSign, doubledOperator]

/-- Full matrix graded anticommutator `{Γ,D_K}=0`. -/
theorem grading_anticommute_doubledOperator
    (K : Matrix (Fin n) (Fin n) ℝ) :
    gradingMatrix n * doubledOperator K +
      doubledOperator K * gradingMatrix n = 0 := by
  rw [gradingMatrix_mul_eq_gradeLeft, mul_gradingMatrix_eq_gradeRight,
    doubledOperator_grade_reversing]
  simp

/-- Equivalently, conjugation by the grading flips the doubled operator. -/
theorem grading_conjugates_doubledOperator_to_neg
    (K : Matrix (Fin n) (Fin n) ℝ) :
    gradingMatrix n * doubledOperator K * gradingMatrix n =
      -doubledOperator K := by
  have hanti := grading_anticommute_doubledOperator (n := n) K
  have hleft :
      gradingMatrix n * doubledOperator K =
        -(doubledOperator K * gradingMatrix n) := by
    exact eq_neg_of_add_eq_zero_left hanti
  rw [hleft]
  simp only [neg_mul, Matrix.mul_assoc, gradingMatrix_sq, Matrix.mul_one]

/-- Neutral bridge into the repository's existing primal/dual spectral token. -/
def forwardReverseToken {V : Type*} (forward reverse : V) :
    InfoGeometry.LLM.SpectralToken.SpectralToken V :=
  ⟨forward, reverse⟩

@[simp] theorem forwardReverseToken_swap {V : Type*} (forward reverse : V) :
    InfoGeometry.LLM.SpectralToken.SpectralToken.swap
      (forwardReverseToken forward reverse) =
    forwardReverseToken reverse forward := by
  rfl

end InfoGeometry.MassSpectrometry
