import InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices

Sparse finite templates for the `n = 7` and `n = 8` Fibonacci braid matrices.

The paper displays large `8 × 8` and `13 × 13` matrices.  Rather than
transcribing those dense matrices entry-by-entry, this file records the same
finite information as sparse templates:

* diagonal singlet phases `q⁻⁴` and `q³`;
* positions of each symbolic two-by-two `B` block;
* a reconstruction function turning those data into a matrix.

This is a finite algebraic template layer only.
No conformal-block construction.
No analytic continuation.
No all-`n` Artin-relation proof.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices

open Matrix
open FiniteFibonacciLowAnyonMatrices

/-- Channel index for the `d₇ = 8` basis. -/
abbrev Basis7 := Fin 8

/-- Channel index for the `d₈ = 13` basis. -/
abbrev Basis8 := Fin 13

/-- Entry contributed by one symbolic `B` block on coordinates `(a,b)`. -/
def blockEntry? {d : ℕ} (B : BBlockEntries) (a b i j : Fin d) : Option ℂ :=
  if i = a then
    if j = a then some (BBlockEntries.B00 B) else if j = b then some (BBlockEntries.B01 B) else some 0
  else if i = b then
    if j = a then some (BBlockEntries.B10 B) else if j = b then some (BBlockEntries.B11 B) else some 0
  else if j = a ∨ j = b then
    some 0
  else
    none

/-- Entry contributed by a list of symbolic `B` blocks. -/
def blockEntries? {d : ℕ} (B : BBlockEntries) :
    List (Fin d × Fin d) → Fin d → Fin d → Option ℂ
  | [], _, _ => none
  | (a, b) :: rest, i, j =>
      match blockEntry? B a b i j with
      | some x => some x
      | none => blockEntries? B rest i j

/-- Reconstruct a sparse braid matrix from diagonal phases and symbolic `B` blocks. -/
noncomputable def sparseBraidMatrix {d : ℕ}
    (phase : Fin d → ℂ) (blocks : List (Fin d × Fin d)) (B : BBlockEntries) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    match blockEntries? B blocks i j with
    | some x => x
    | none => if i = j then phase i else 0

/-- If there are no `B` blocks, the sparse matrix is diagonal. -/
theorem sparseBraidMatrix_nil_apply {d : ℕ}
    (phase : Fin d → ℂ) (B : BBlockEntries) (i j : Fin d) :
    sparseBraidMatrix phase [] B i j = if i = j then phase i else 0 :=
  rfl

/-- The upper-left entry of a one-block sparse matrix. -/
theorem sparseBraidMatrix_single_B00 {d : ℕ}
    (phase : Fin d → ℂ) (B : BBlockEntries) (a b : Fin d) :
    sparseBraidMatrix phase [(a, b)] B a a = B.B00 := by
  simp [sparseBraidMatrix, blockEntries?, blockEntry?]

/-- The upper-right entry of a one-block sparse matrix. -/
theorem sparseBraidMatrix_single_B01 {d : ℕ}
    (phase : Fin d → ℂ) (B : BBlockEntries) {a b : Fin d} (hab : b ≠ a) :
    sparseBraidMatrix phase [(a, b)] B a b = B.B01 := by
  simp [sparseBraidMatrix, blockEntries?, blockEntry?, hab]

/-- The lower-left entry of a one-block sparse matrix. -/
theorem sparseBraidMatrix_single_B10 {d : ℕ}
    (phase : Fin d → ℂ) (B : BBlockEntries) {a b : Fin d} (hab : a ≠ b) :
    sparseBraidMatrix phase [(a, b)] B b a = B.B10 := by
  have hba : b ≠ a := fun h => hab h.symm
  simp [sparseBraidMatrix, blockEntries?, blockEntry?, hba]

/-- The lower-right entry of a one-block sparse matrix. -/
theorem sparseBraidMatrix_single_B11 {d : ℕ}
    (phase : Fin d → ℂ) (B : BBlockEntries) {a b : Fin d} (hab : b ≠ a) :
    sparseBraidMatrix phase [(a, b)] B b b = B.B11 := by
  simp [sparseBraidMatrix, blockEntries?, blockEntry?, hab]

/-- Diagonal phase vector for `π₇(b₁)`. -/
def pi7_b1_phase (qNeg4 q3 : ℂ) : Basis7 → ℂ :=
  ![q3, qNeg4, q3, qNeg4, q3, q3, qNeg4, q3]

/-- Diagonal phase vector for `π₇(b₆)`. -/
def pi7_b6_phase (qNeg4 q3 : ℂ) : Basis7 → ℂ :=
  ![qNeg4, qNeg4, qNeg4, q3, q3, q3, q3, q3]

/-- Sparse `π₇(b₁)`. -/
noncomputable def pi7_b1 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis7 Basis7 ℂ :=
  sparseBraidMatrix (pi7_b1_phase qNeg4 q3) [] B

/-- Sparse `π₇(b₂)`. -/
noncomputable def pi7_b2 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis7 Basis7 ℂ :=
  sparseBraidMatrix (fun _ => q3) [((1 : Basis7), 2), (3, 4), (6, 7)] B

/-- Sparse `π₇(b₃)`. -/
noncomputable def pi7_b3 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis7 Basis7 ℂ :=
  sparseBraidMatrix (pi7_b1_phase qNeg4 q3) [((0 : Basis7), 2), (5, 7)] B

/-- Sparse `π₇(b₄)`. -/
noncomputable def pi7_b4 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis7 Basis7 ℂ :=
  sparseBraidMatrix (pi7_b1_phase qNeg4 q3) [((3 : Basis7), 6), (4, 7)] B

/-- Sparse `π₇(b₅)`. -/
noncomputable def pi7_b5 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis7 Basis7 ℂ :=
  sparseBraidMatrix (fun _ => q3) [((0 : Basis7), 5), (1, 6), (2, 7)] B

/-- Sparse `π₇(b₆)`. -/
noncomputable def pi7_b6 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis7 Basis7 ℂ :=
  sparseBraidMatrix (pi7_b6_phase qNeg4 q3) [] B

/-- Diagonal phase vector for `π₈(b₁)`. -/
def pi8_b1_phase (qNeg4 q3 : ℂ) : Basis8 → ℂ :=
  ![qNeg4, q3, q3, qNeg4, q3, q3, qNeg4, q3, qNeg4, q3, q3, qNeg4, q3]

/-- Diagonal phase vector for `π₈(b₇)`. -/
def pi8_b7_phase (qNeg4 q3 : ℂ) : Basis8 → ℂ :=
  ![qNeg4, qNeg4, qNeg4, qNeg4, qNeg4, q3, q3, q3, q3, q3, q3, q3, q3]

/-- Sparse `π₈(b₁)`. -/
noncomputable def pi8_b1 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (pi8_b1_phase qNeg4 q3) [] B

/-- Sparse `π₈(b₂)`. -/
noncomputable def pi8_b2 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (fun _ => q3)
    [((0 : Basis8), 1), (3, 4), (6, 7), (8, 9), (11, 12)] B

/-- Sparse `π₈(b₃)`. -/
noncomputable def pi8_b3 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (pi8_b1_phase qNeg4 q3) [((2 : Basis8), 4), (5, 7), (10, 12)] B

/-- Sparse `π₈(b₄)`. -/
noncomputable def pi8_b4 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (pi8_b1_phase qNeg4 q3)
    [((0 : Basis8), 3), (1, 4), (8, 11), (9, 12)] B

/-- Sparse `π₈(b₅)`. -/
noncomputable def pi8_b5 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (pi8_b7_phase qNeg4 q3) [((5 : Basis8), 10), (6, 11), (7, 12)] B

/-- Sparse `π₈(b₆)`. -/
noncomputable def pi8_b6 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (fun _ => q3)
    [((0 : Basis8), 8), (1, 9), (2, 10), (3, 11), (4, 12)] B

/-- Sparse `π₈(b₇)`. -/
noncomputable def pi8_b7 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis8 Basis8 ℂ :=
  sparseBraidMatrix (pi8_b7_phase qNeg4 q3) [] B

/-- Example: `π₇(b₂)` has a `B` block on coordinates `(1,2)`. -/
theorem pi7_b2_first_block (q3 : ℂ) (B : BBlockEntries) :
    pi7_b2 q3 B 1 1 = BBlockEntries.B00 B ∧ pi7_b2 q3 B 1 2 = BBlockEntries.B01 B ∧
      pi7_b2 q3 B 2 1 = BBlockEntries.B10 B ∧ pi7_b2 q3 B 2 2 = BBlockEntries.B11 B := by
  simp [pi7_b2, sparseBraidMatrix, blockEntries?, blockEntry?]

/-- Example: `π₈(b₆)` has a `B` block on coordinates `(0,8)`. -/
theorem pi8_b6_first_block (q3 : ℂ) (B : BBlockEntries) :
    pi8_b6 q3 B 0 0 = BBlockEntries.B00 B ∧ pi8_b6 q3 B 0 8 = BBlockEntries.B01 B ∧
      pi8_b6 q3 B 8 0 = BBlockEntries.B10 B ∧ pi8_b6 q3 B 8 8 = BBlockEntries.B11 B := by
  simp [pi8_b6, sparseBraidMatrix, blockEntries?, blockEntry?]

end InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices
