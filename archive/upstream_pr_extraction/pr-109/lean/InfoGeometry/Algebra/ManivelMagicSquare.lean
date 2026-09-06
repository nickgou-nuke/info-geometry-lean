import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Laurent Manivel's Tits-Freudenthal Magic-Square Dimension Ledger

This module formalizes the Tits-Freudenthal Magic Square of Lie algebras, the Jordan
algebras $\mathcal{H}_3(\mathbb{A})$, and the Vinberg-Manivel triality construction from:

  **Laurent Manivel**, *BRIDGES Lectures: $G_2$ in action, and a mathematical theory of exceptions*,
  HAL Id: hal-05212903, May 2025 (Section 4).

### Scope boundary:
The `NormedAlg` enum below is an index for dimension bookkeeping. It is not a
concrete composition-algebra carrier, and this file does not construct Lie
brackets, Jacobi proofs, root data, or real-form identifications. Split-real
claims belong to the concrete split-octonion and split-Albert owners.

### Key Mathematical Structures:
1. **Composition-Algebra Dimension Index**:
   $\mathbb{A} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}\}$ with dimensions $a \in \{1, 2, 4, 8\}$.
2. **Hermitian Jordan Algebra $\mathcal{H}_3(\mathbb{A})$**:
   - Total dimension: $\dim \mathcal{H}_3(\mathbb{A}) = 3 + 3 a$.
   - Traceless subspace dimension: $\dim \mathcal{H}_3(\mathbb{A})_0 = 2 + 3 a$.
   - For Albert algebra $\mathcal{H}_3(\mathbb{O})$: $\dim = 27$ and $\dim_0 = 26$.
3. **Tits-Freudenthal Construction Formula**:
   $$\mathfrak{L}(\mathbb{A}, \mathbb{B}) = \operatorname{Der}(\mathbb{A}) \oplus \operatorname{Der}(\mathcal{H}_3(\mathbb{B})) \oplus (\operatorname{Im}(\mathbb{A}) \otimes \mathcal{H}_3(\mathbb{B})_0)$$
   with exact dimension formula:
   $$\dim \mathfrak{L}(\mathbb{A}, \mathbb{B}) = \dim \operatorname{Der}(\mathbb{A}) + \dim \operatorname{Der}(\mathcal{H}_3(\mathbb{B})) + (a - 1)(2 + 3 b).$$
4. **Dimension table for the 16 classical type entries**:
   - Row 1 ($\mathbb{R}$): $\mathfrak{so}_3 (3)$, $\mathfrak{sl}_3 (8)$, $\mathfrak{sp}_6 (21)$, $\mathfrak{f}_4 (52)$
   - Row 2 ($\mathbb{C}$): $\mathfrak{sl}_3 (8)$, $\mathfrak{sl}_3 \oplus \mathfrak{sl}_3 (16)$, $\mathfrak{sl}_6 (35)$, $\mathfrak{e}_6 (78)$
   - Row 3 ($\mathbb{H}$): $\mathfrak{sp}_6 (21)$, $\mathfrak{sl}_6 (35)$, $\mathfrak{so}_{12} (66)$, $\mathfrak{e}_7 (133)$
   - Row 4 ($\mathbb{O}$): $\mathfrak{f}_4 (52)$, $\mathfrak{e}_6 (78)$, $\mathfrak{e}_7 (133)$, $\mathfrak{e}_8 (248)$
5. **Vinberg Symmetric Triality Construction**:
   $$\mathfrak{L}_{sym}(\mathbb{A}, \mathbb{B}) = \mathfrak{tri}(\mathbb{A}) \oplus \mathfrak{tri}(\mathbb{B}) \oplus \bigoplus_{i=1}^3 (\mathbb{A}_i \otimes \mathbb{B}_i)$$
   yielding $\dim \mathfrak{e}_8 = 28 + 28 + 3 \times 64 = 56 + 192 = 248$.

All proofs are 100% native Lean 4 / Mathlib with 0 sorrys and 0 custom axioms.
The resulting equalities are dimension statements, not Lie-algebra
isomorphism theorems without additional concrete carriers and brackets.
-/

namespace InfoGeometry.Algebra.ManivelMagicSquare

/-- The four composition algebra types: $\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}$. -/
inductive NormedAlg
  | R : NormedAlg
  | C : NormedAlg
  | H : NormedAlg
  | O : NormedAlg
  deriving DecidableEq, Repr

namespace NormedAlg

/-- The dimension $a = \dim \mathbb{A} \in \{1, 2, 4, 8\}$. -/
def dim : NormedAlg → ℕ
  | R => 1
  | C => 2
  | H => 4
  | O => 8

/-- The imaginary dimension $a - 1 = \dim \operatorname{Im}(\mathbb{A}) \in \{0, 1, 3, 7\}$. -/
def dimIm : NormedAlg → ℕ
  | R => 0
  | C => 1
  | H => 3
  | O => 7

/-- The derivation algebra dimension $\dim \operatorname{Der}(\mathbb{A}) \in \{0, 0, 3, 14\}$. -/
def dimDer : NormedAlg → ℕ
  | R => 0
  | C => 0
  | H => 3
  | O => 14

/-- The derivation algebra dimension of $\mathcal{H}_3(\mathbb{A})$: $\{3, 8, 21, 52\}$. -/
def dimDerH3 : NormedAlg → ℕ
  | R => 3
  | C => 8
  | H => 21
  | O => 52

/-- The triality Lie algebra dimension $\dim \mathfrak{tri}(\mathbb{A}) \in \{0, 2, 9, 28\}$. -/
def dimTri : NormedAlg → ℕ
  | R => 0
  | C => 2
  | H => 9
  | O => 28

end NormedAlg

/-! =========================================================================
    1. Hermitian Jordan Algebra $\mathcal{H}_3(\mathbb{A})$ Dimensions
    ========================================================================= -/

/-- Total dimension of the Hermitian Jordan algebra $\mathcal{H}_3(\mathbb{A})$: $3 + 3 a$. -/
def dimH3 (A : NormedAlg) : ℕ :=
  3 + 3 * A.dim

/-- Traceless dimension of $\mathcal{H}_3(\mathbb{A})_0$: $2 + 3 a$. -/
def dimH3Zero (A : NormedAlg) : ℕ :=
  2 + 3 * A.dim

/-- The Albert algebra $\mathcal{H}_3(\mathbb{O})$ has dimension 27. -/
theorem albert_algebra_dimension : dimH3 NormedAlg.O = 27 := rfl

/-- The traceless Albert sector has dimension 26. -/
theorem albert_traceless_dimension : dimH3Zero NormedAlg.O = 26 := rfl

/-! =========================================================================
    2. Tits-Freudenthal Magic Square Dimension Formula
    ========================================================================= -/

/-- The Tits-Freudenthal Lie algebra dimension $\dim \mathfrak{L}(\mathbb{A}, \mathbb{B})$. -/
def titsFreudenthalDim (A B : NormedAlg) : ℕ :=
  A.dimDer + B.dimDerH3 + A.dimIm * (dimH3Zero B)

theorem magic_square_row1_R : titsFreudenthalDim NormedAlg.R NormedAlg.R = 3 := rfl
theorem magic_square_row1_C : titsFreudenthalDim NormedAlg.R NormedAlg.C = 8 := rfl
theorem magic_square_row1_H : titsFreudenthalDim NormedAlg.R NormedAlg.H = 21 := rfl
theorem magic_square_row1_O : titsFreudenthalDim NormedAlg.R NormedAlg.O = 52 := rfl

theorem magic_square_row2_R : titsFreudenthalDim NormedAlg.C NormedAlg.R = 8 := rfl
theorem magic_square_row2_C : titsFreudenthalDim NormedAlg.C NormedAlg.C = 16 := rfl
theorem magic_square_row2_H : titsFreudenthalDim NormedAlg.C NormedAlg.H = 35 := rfl
theorem magic_square_row2_O : titsFreudenthalDim NormedAlg.C NormedAlg.O = 78 := rfl

theorem magic_square_row3_R : titsFreudenthalDim NormedAlg.H NormedAlg.R = 21 := rfl
theorem magic_square_row3_C : titsFreudenthalDim NormedAlg.H NormedAlg.C = 35 := rfl
theorem magic_square_row3_H : titsFreudenthalDim NormedAlg.H NormedAlg.H = 66 := rfl
theorem magic_square_row3_O : titsFreudenthalDim NormedAlg.H NormedAlg.O = 133 := rfl

theorem magic_square_row4_R : titsFreudenthalDim NormedAlg.O NormedAlg.R = 52 := rfl
theorem magic_square_row4_C : titsFreudenthalDim NormedAlg.O NormedAlg.C = 78 := rfl
theorem magic_square_row4_H : titsFreudenthalDim NormedAlg.O NormedAlg.H = 133 := rfl
theorem magic_square_row4_O : titsFreudenthalDim NormedAlg.O NormedAlg.O = 248 := rfl

/-- The Magic Square is symmetric in dimensions. -/
theorem magic_square_symmetric (A B : NormedAlg) :
    titsFreudenthalDim A B = titsFreudenthalDim B A := by
  cases A <;> cases B <;> rfl

/-! =========================================================================
    3. Vinberg Symmetric Triality Construction
    ========================================================================= -/

/-- Dimension of the Vinberg symmetric triality construction:
    $\dim \mathfrak{L}_{sym}(\mathbb{A}, \mathbb{B}) = \dim \mathfrak{tri}(\mathbb{A}) + \dim \mathfrak{tri}(\mathbb{B}) + 3 a b$. -/
def vinbergTrialityDim (A B : NormedAlg) : ℕ :=
  A.dimTri + B.dimTri + 3 * (A.dim * B.dim)

theorem vinberg_e8_dimension :
    vinbergTrialityDim NormedAlg.O NormedAlg.O = 248 := rfl

theorem vinberg_e7_dimension :
    vinbergTrialityDim NormedAlg.H NormedAlg.O = 133 := rfl

theorem vinberg_e6_dimension :
    vinbergTrialityDim NormedAlg.C NormedAlg.O = 78 := rfl

theorem vinberg_f4_dimension :
    vinbergTrialityDim NormedAlg.R NormedAlg.O = 52 := rfl

/-- Equivalence of Tits-Freudenthal and Vinberg triality dimensions across all 16 cells. -/
theorem tits_freudenthal_vinberg_dimension_eq (A B : NormedAlg) :
    titsFreudenthalDim A B = vinbergTrialityDim A B := by
  cases A <;> cases B <;> rfl

/-! =========================================================================
    4. Correct dimension bookkeeping for the exceptional Jordan/FTS tower
    ========================================================================= -/

/-- The split Albert derivation algebra has the $F_4$ dimension 52. -/
def albertDerivationDim : ℕ := NormedAlg.O.dimDerH3

/-- The reduced structure algebra adds the 26-dimensional traceless Albert sector. -/
def albertReducedStructureDim : ℕ :=
  albertDerivationDim + dimH3Zero NormedAlg.O

/-- The grade-zero algebra in the conformal/TKK 3-grading contains the reduced
structure algebra together with the one-dimensional grading/dilation generator. -/
def albertTKKGradeZeroDim : ℕ :=
  albertReducedStructureDim + 1

/-- The Freudenthal charge space $\mathbb R \oplus \mathbb R \oplus J \oplus J$
has dimension $2 + 2\dim J$. -/
def freudenthalChargeDim (A : NormedAlg) : ℕ :=
  2 + 2 * dimH3 A

@[simp] theorem albert_derivation_dimension :
    albertDerivationDim = 52 := rfl

@[simp] theorem albert_reduced_structure_dimension :
    albertReducedStructureDim = 78 := rfl

@[simp] theorem albert_tkk_grade_zero_dimension :
    albertTKKGradeZeroDim = 79 := rfl

@[simp] theorem split_albert_freudenthal_charge_dimension :
    freudenthalChargeDim NormedAlg.O = 56 := rfl

/-- Correct $E_7$ TKK dimension bookkeeping:
`27 + (78 + 1) + 27 = 133`, not `27 + 78 + 27`. -/
theorem e7_tkk_dimension_decomposition :
    dimH3 NormedAlg.O + albertTKKGradeZeroDim + dimH3 NormedAlg.O = 133 := rfl

/-- The reduced structure contribution itself is exactly the $E_6$ dimension. -/
theorem e6_reduced_structure_dimension_matches_magic_square :
    albertReducedStructureDim = titsFreudenthalDim NormedAlg.C NormedAlg.O := by
  rfl

/-- The TKK three-grading dimension agrees with the $E_7$ magic-square cell. -/
theorem e7_tkk_dimension_matches_magic_square :
    dimH3 NormedAlg.O + albertTKKGradeZeroDim + dimH3 NormedAlg.O =
      titsFreudenthalDim NormedAlg.H NormedAlg.O := by
  rfl

/-- Correct $E_8$ decomposition under $E_7 \times \mathfrak{sl}_2$:
`248 = 133 + 2 * 56 + 3`.  The `56` occurs as an $\mathfrak{sl}_2$ doublet,
so a single copy would undercount the algebra. -/
theorem e8_e7_freudenthal_sl2_dimension_decomposition :
    133 + 2 * freudenthalChargeDim NormedAlg.O + 3 = 248 := by
  rfl

/-- The $E_8$ Freudenthal/$\mathfrak{sl}_2$ bookkeeping agrees with the
octonion-octonion Vinberg cell. -/
theorem e8_freudenthal_dimension_matches_vinberg :
    133 + 2 * freudenthalChargeDim NormedAlg.O + 3 =
      vinbergTrialityDim NormedAlg.O NormedAlg.O := by
  rfl

/-- The symmetric Vinberg formula has three tensor copies.  For the octonion
cell this is `28 + 28 + 3 * (8 * 8) = 248`. -/
theorem e8_vinberg_three_tensor_copies :
    NormedAlg.O.dimTri + NormedAlg.O.dimTri +
        3 * (NormedAlg.O.dim * NormedAlg.O.dim) = 248 := by
  rfl

end InfoGeometry.Algebra.ManivelMagicSquare
