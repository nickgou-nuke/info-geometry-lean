import InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices

/-!
# InfoGeometry.Canonical.FiniteFibonacciGeneralBraidGenerators

Finite general braid-generator templates for Fibonacci anyons.

Section 7 of the paper describes the recursive shape of the `Bₙ` generator
matrices.  This file formalizes that finite algebraic shape without claiming an
analytic conformal-block construction or an all-`n` Artin-relation proof.

The formalized content is:

* the shifted Fibonacci dimensions `dₙ = fib (n - 1)`;
* block-diagonal restriction templates `πₙ(bᵢ) = πₙ₋₂(bᵢ) ⊕ πₙ₋₁(bᵢ)`;
* the three-block refinement of equation `(7.2)`;
* the last-two-generator block templates of equation `(7.3)`;
* the determinant-exponent Fibonacci recurrence at the symbolic exponent level.

No monodromy recursion theorem.
No analytic continuation.
No concrete proof of all Artin relations.
-/

namespace FiniteFibonacciGeneralBraidGenerators

open Matrix
open FiniteFibonacciLowAnyonMatrices

/-- Shifted Fibonacci dimension `dₙ` with `d₂ = d₃ = 1`. -/
def fibonacciBlockDimension (n : ℕ) : ℕ :=
  Nat.fib (n - 1)

@[simp]
theorem fibonacciBlockDimension_two :
    fibonacciBlockDimension 2 = 1 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

@[simp]
theorem fibonacciBlockDimension_three :
    fibonacciBlockDimension 3 = 1 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

@[simp]
theorem fibonacciBlockDimension_four :
    fibonacciBlockDimension 4 = 2 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

@[simp]
theorem fibonacciBlockDimension_five :
    fibonacciBlockDimension 5 = 3 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

@[simp]
theorem fibonacciBlockDimension_six :
    fibonacciBlockDimension 6 = 5 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

@[simp]
theorem fibonacciBlockDimension_seven :
    fibonacciBlockDimension 7 = 8 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

@[simp]
theorem fibonacciBlockDimension_eight :
    fibonacciBlockDimension 8 = 13 := by
  norm_num [fibonacciBlockDimension, Nat.fib]

/-- Shifted Fibonacci recurrence for the dimensions, in the stable range. -/
theorem fibonacciBlockDimension_step (k : ℕ) :
    fibonacciBlockDimension (k + 4) =
      fibonacciBlockDimension (k + 2) + fibonacciBlockDimension (k + 3) := by
  unfold fibonacciBlockDimension
  have h₁ : k + 4 - 1 = k + 3 := by omega
  have h₂ : k + 2 - 1 = k + 1 := by omega
  have h₃ : k + 3 - 1 = k + 2 := by omega
  rw [h₁, h₂, h₃]
  exact Nat.fib_add_two

/-- Two-block direct sum index. -/
abbrev TwoBlockIndex (a b : ℕ) := Fin a ⊕ Fin b

/-- Three-block index matching `dₙ₋₂ ⊕ dₙ₋₃ ⊕ dₙ₋₂`. -/
abbrev ThreeBlockIndex (a b : ℕ) := Fin a ⊕ (Fin b ⊕ Fin a)

/-- Block-diagonal two-summand matrix template. -/
noncomputable def twoBlockDiagonal {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (TwoBlockIndex a b) (TwoBlockIndex a b) ℂ
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inr i, Sum.inr j => C i j
  | _, _ => 0

/-- Equation `(7.1)` as a finite block-diagonal template. -/
theorem twoBlockDiagonal_left_apply {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin a) :
    twoBlockDiagonal A C (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

/-- The lower-right block in equation `(7.1)`. -/
theorem twoBlockDiagonal_right_apply {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin b) :
    twoBlockDiagonal A C (Sum.inr i) (Sum.inr j) = C i j :=
  rfl

/-- Off-diagonal blocks vanish in the two-block restriction template. -/
theorem twoBlockDiagonal_off_apply {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ)
    (i : Fin a) (j : Fin b) :
    twoBlockDiagonal A C (Sum.inl i) (Sum.inr j) = 0 ∧
      twoBlockDiagonal A C (Sum.inr j) (Sum.inl i) = 0 :=
  ⟨rfl, rfl⟩

/-- Three-block refinement template of equation `(7.2)`. -/
noncomputable def threeBlockDiagonal {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (ThreeBlockIndex a b) (ThreeBlockIndex a b) ℂ
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => C i j
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => A i j
  | _, _ => 0

/-- First copy in the three-block refinement. -/
theorem threeBlockDiagonal_first_apply {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin a) :
    threeBlockDiagonal A C (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

/-- Middle block in the three-block refinement. -/
theorem threeBlockDiagonal_middle_apply {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin b) :
    threeBlockDiagonal A C (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) = C i j :=
  rfl

/-- Last copy in the three-block refinement. -/
theorem threeBlockDiagonal_last_apply {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (C : Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin a) :
    threeBlockDiagonal A C (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = A i j :=
  rfl

/-- Last-but-one generator template in equation `(7.3)`. -/
noncomputable def lastButOneGenerator {a b : ℕ} (q3 : ℂ) (B : BBlockEntries) :
    Matrix (ThreeBlockIndex a b) (ThreeBlockIndex a b) ℂ
  | Sum.inl i, Sum.inl j => if i = j then B.B00 else 0
  | Sum.inl i, Sum.inr (Sum.inr j) => if i = j then B.B01 else 0
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => if i = j then q3 else 0
  | Sum.inr (Sum.inr i), Sum.inl j => if i = j then B.B10 else 0
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => if i = j then B.B11 else 0
  | _, _ => 0

/-- Top-left scalar identity block of the last-but-one generator. -/
theorem lastButOneGenerator_B00 {a b : ℕ} (q3 : ℂ) (B : BBlockEntries) (i : Fin a) :
    lastButOneGenerator (a := a) (b := b) q3 B (Sum.inl i) (Sum.inl i) = B.B00 := by
  simp [lastButOneGenerator]

/-- Top-right scalar identity block of the last-but-one generator. -/
theorem lastButOneGenerator_B01 {a b : ℕ} (q3 : ℂ) (B : BBlockEntries) (i : Fin a) :
    lastButOneGenerator (a := a) (b := b) q3 B (Sum.inl i) (Sum.inr (Sum.inr i)) = B.B01 := by
  simp [lastButOneGenerator]

/-- Middle scalar identity block of the last-but-one generator. -/
theorem lastButOneGenerator_middle {a b : ℕ} (q3 : ℂ) (B : BBlockEntries) (i : Fin b) :
    lastButOneGenerator (a := a) (b := b) q3 B (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) = q3 := by
  simp [lastButOneGenerator]

/-- Bottom-left scalar identity block of the last-but-one generator. -/
theorem lastButOneGenerator_B10 {a b : ℕ} (q3 : ℂ) (B : BBlockEntries) (i : Fin a) :
    lastButOneGenerator (a := a) (b := b) q3 B (Sum.inr (Sum.inr i)) (Sum.inl i) = B.B10 := by
  simp [lastButOneGenerator]

/-- Bottom-right scalar identity block of the last-but-one generator. -/
theorem lastButOneGenerator_B11 {a b : ℕ} (q3 : ℂ) (B : BBlockEntries) (i : Fin a) :
    lastButOneGenerator (a := a) (b := b) q3 B (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) = B.B11 := by
  simp [lastButOneGenerator]

/-- Last generator template in equation `(7.3)`. -/
noncomputable def lastGenerator {a b : ℕ} (qNeg4 q3 : ℂ) :
    Matrix (ThreeBlockIndex a b) (ThreeBlockIndex a b) ℂ
  | Sum.inl i, Sum.inl j => if i = j then qNeg4 else 0
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => if i = j then q3 else 0
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => if i = j then q3 else 0
  | _, _ => 0

/-- First block of the last generator carries `q⁻⁴`. -/
theorem lastGenerator_first {a b : ℕ} (qNeg4 q3 : ℂ) (i : Fin a) :
    lastGenerator (a := a) (b := b) qNeg4 q3 (Sum.inl i) (Sum.inl i) = qNeg4 := by
  simp [lastGenerator]

/-- Middle block of the last generator carries `q³`. -/
theorem lastGenerator_middle {a b : ℕ} (qNeg4 q3 : ℂ) (i : Fin b) :
    lastGenerator (a := a) (b := b) qNeg4 q3 (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) = q3 := by
  simp [lastGenerator]

/-- Last block of the last generator carries `q³`. -/
theorem lastGenerator_last {a b : ℕ} (qNeg4 q3 : ℂ) (i : Fin a) :
    lastGenerator (a := a) (b := b) qNeg4 q3 (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) = q3 := by
  simp [lastGenerator]

/-- Symbolic determinant exponent recurrence, offset so `e 0 = D₂`, `e 1 = D₃`. -/
def determinantExponent : ℕ → ℤ
  | 0 => -4
  | 1 => 3
  | k + 2 => determinantExponent k + determinantExponent (k + 1)

@[simp]
theorem determinantExponent_zero : determinantExponent 0 = -4 :=
  rfl

@[simp]
theorem determinantExponent_one : determinantExponent 1 = 3 :=
  rfl

/-- Determinant exponents satisfy the same Fibonacci recurrence. -/
theorem determinantExponent_step (k : ℕ) :
    determinantExponent (k + 2) = determinantExponent k + determinantExponent (k + 1) :=
  rfl

/-- First determinant exponent examples, before reducing powers using `q^10 = 1`. -/
theorem determinantExponent_first_examples :
    determinantExponent 2 = -1 ∧ determinantExponent 3 = 2 ∧
      determinantExponent 4 = 1 ∧ determinantExponent 5 = 3 := by
  norm_num [determinantExponent]

end FiniteFibonacciGeneralBraidGenerators
