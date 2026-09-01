import Mathlib
import InfoGeometry.MassSpectrometry.Core

/-!
# Operator geometry for finite mass-spectrometry representations

This module formalizes the representation-independent matrix identities behind
three useful spectral constructions:

* symmetric/antisymmetric decomposition of a directed correlation operator;
* a Gram operator, whose antisymmetric component vanishes identically;
* a doubled left/right carrier for forward and inverse channels.

The terminology is algebraic.  No claim is made that physical molecular
fragments are Majorana modes or that a learned attention matrix is a Gram
matrix.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix

variable {n d : ℕ}

/-! ## Symmetric and antisymmetric directed correlations -/

/-- Reciprocal part of a finite directed correlation operator. -/
def symmetricPart (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (K + K.transpose)

/-- Oriented part of a finite directed correlation operator. -/
def antisymmetricPart (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (K - K.transpose)

/-- Every real square matrix is exactly reconstructed from its reciprocal and
oriented parts. -/
theorem symmetricPart_add_antisymmetricPart
    (K : Matrix (Fin n) (Fin n) ℝ) :
    symmetricPart K + antisymmetricPart K = K := by
  ext i j
  simp [symmetricPart, antisymmetricPart]
  ring

/-- The reciprocal component is symmetric. -/
theorem symmetricPart_transpose
    (K : Matrix (Fin n) (Fin n) ℝ) :
    (symmetricPart K).transpose = symmetricPart K := by
  ext i j
  simp [symmetricPart, add_comm]

/-- The oriented component changes sign under transposition. -/
theorem antisymmetricPart_transpose
    (K : Matrix (Fin n) (Fin n) ℝ) :
    (antisymmetricPart K).transpose = -antisymmetricPart K := by
  ext i j
  simp [antisymmetricPart]
  ring

/-! ## Gram operators -/

/-- Row Gram operator of a finite feature matrix. -/
def gramOperator (Z : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Z * Z.transpose

/-- A genuine real Gram operator is symmetric. -/
theorem gramOperator_transpose
    (Z : Matrix (Fin n) (Fin d) ℝ) :
    (gramOperator Z).transpose = gramOperator Z := by
  simp [gramOperator, Matrix.transpose_mul]

/-- Therefore a real Gram operator has no antisymmetric component. -/
theorem antisymmetricPart_gramOperator_eq_zero
    (Z : Matrix (Fin n) (Fin d) ℝ) :
    antisymmetricPart (gramOperator Z) = 0 := by
  ext i j
  simp [antisymmetricPart, gramOperator_transpose]

/-! ## Left/right doubled carrier -/

/-- Two labelled copies of a finite spectral state space. -/
abbrev DoubledIndex (n : ℕ) := Sum (Fin n) (Fin n)

/-- Off-diagonal doubling of a directed operator `K`, with the reverse block
represented by `Kᵀ`. -/
def doubledOperator (K : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ := fun i j =>
  match i, j with
  | Sum.inl a, Sum.inr b => K a b
  | Sum.inr a, Sum.inl b => K b a
  | _, _ => 0

/-- The doubled operator is symmetric even when the original directed
operator is not. -/
theorem doubledOperator_transpose
    (K : Matrix (Fin n) (Fin n) ℝ) :
    (doubledOperator K).transpose = doubledOperator K := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Sign of the left/right grading. -/
def doubledSign : DoubledIndex n → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- Left action of the grading sign. -/
def gradeLeft (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  fun i j => doubledSign i * A i j

/-- Right action of the grading sign. -/
def gradeRight (A : Matrix (DoubledIndex n) (DoubledIndex n) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  fun i j => A i j * doubledSign j

/-- The doubled off-diagonal operator reverses the left/right grading.  This
is the elementwise form of anticommutation with the diagonal grading matrix. -/
theorem doubledOperator_grade_reversing
    (K : Matrix (Fin n) (Fin n) ℝ) :
    gradeLeft (doubledOperator K) = -gradeRight (doubledOperator K) := by
  ext i j
  cases i <;> cases j <;>
    simp [gradeLeft, gradeRight, doubledSign, doubledOperator]

end InfoGeometry.MassSpectrometry
