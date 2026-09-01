import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
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

def gradeLeft (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  fun i j => doubledSign i * A i j

def gradeRight (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  fun i j => A i j * doubledSign j

/-- The off-diagonal doubling reverses the two-lane grading. -/
theorem doubledOperator_grade_reversing
    (K : Matrix (Fin n) (Fin n) ℝ) :
    gradeLeft (doubledOperator K) = -gradeRight (doubledOperator K) := by
  ext i j
  cases i <;> cases j <;>
    simp [gradeLeft, gradeRight, doubledSign, doubledOperator]

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
