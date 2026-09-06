import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Finite neutral Krein--Majorana frame

This is the native finite-dimensional frame for a doubled real carrier
`V₊ ⊕ V₋`, indexed by `Fin n ⊕ Fin n`.  The symmetric neutral form `η` and
the skew Majorana form `Ω` are separate data.  The matrices below are the
canonical Witt-basis model; no general Pfaffian or operator-algebra theorem is
claimed here.
-/

namespace InfoGeometry.Quantum.NeutralKreinMajoranaFrame

open Matrix

abbrev Carrier (n : ℕ) := Fin n ⊕ Fin n
abbrev Matrix2 (n : ℕ) := Matrix (Carrier n) (Carrier n) ℝ

def kreinMetric (n : ℕ) : Matrix2 n :=
  Matrix.fromBlocks 0 1 1 0

def majoranaForm (n : ℕ) : Matrix2 n :=
  Matrix.fromBlocks 0 1 (-1) 0

def grading (n : ℕ) : Matrix2 n :=
  Matrix.fromBlocks 1 0 0 (-1)

def exchange (n : ℕ) : Matrix2 n :=
  Matrix.fromBlocks 0 1 1 0

def positiveReadout (n : ℕ) : Matrix2 n :=
  kreinMetric n * exchange n

theorem kreinMetric_transpose (n : ℕ) :
    (kreinMetric n).transpose = kreinMetric n := by
  rw [kreinMetric, Matrix.fromBlocks_transpose]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks]

theorem majoranaForm_transpose (n : ℕ) :
    (majoranaForm n).transpose = -(majoranaForm n) := by
  rw [majoranaForm, Matrix.fromBlocks_transpose]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks]

theorem grading_sq (n : ℕ) :
    grading n * grading n = (1 : Matrix2 n) := by
  rw [grading, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem exchange_sq (n : ℕ) :
    exchange n * exchange n = (1 : Matrix2 n) := by
  rw [exchange, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem grading_exchange_anticommute (n : ℕ) :
    grading n * exchange n = -(exchange n * grading n) := by
  rw [grading, exchange, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem kreinMetric_is_neutral (n : ℕ) :
    kreinMetric n = exchange n := rfl

theorem positiveReadout_eq_identity (n : ℕ) :
    positiveReadout n = (1 : Matrix2 n) := by
  rw [positiveReadout, kreinMetric_is_neutral, exchange_sq]

theorem majoranaForm_is_skew (n : ℕ) :
    (majoranaForm n).transpose = -(majoranaForm n) :=
  majoranaForm_transpose n

theorem majoranaForm_squared (n : ℕ) :
    majoranaForm n * majoranaForm n = -(1 : Matrix2 n) := by
  rw [majoranaForm, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem kreinMetric_grading_anti_isometry (n : ℕ) :
    (grading n).transpose * kreinMetric n * grading n = -(kreinMetric n) := by
  unfold grading kreinMetric
  rw [Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem majoranaForm_from_metric_and_grading (n : ℕ) :
    kreinMetric n * majoranaForm n = -(grading n) := by
  unfold kreinMetric majoranaForm grading
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem positiveReadout_self (n : ℕ) (x : Carrier n) :
    (positiveReadout n) x x = (1 : ℝ) := by
  rw [positiveReadout_eq_identity]
  simp

end InfoGeometry.Quantum.NeutralKreinMajoranaFrame
