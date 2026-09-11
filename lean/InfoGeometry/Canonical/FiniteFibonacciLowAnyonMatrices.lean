import InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices

Explicit finite low-anyon braid-matrix templates for Fibonacci anyons.

Section 6 of the paper lists the matrices for `n = 5, 6, 7, 8`.  This file
formalizes the first effective cases, `n = 5` and `n = 6`, as finite symbolic
matrix templates built from the same entries used throughout the finite
interface:

* scalar singlet phases `q⁻⁴` and `q³`;
* a symbolic two-by-two doublet block `B = [[B00, B01], [B10, B11]]`.

The entries are parameters.  This file does not prove that analytic conformal
blocks produce these values, and it does not prove the Artin relations for these
matrices except through explicit theorem hypotheses.

No conformal-block construction.
No analytic continuation.
No all-`n` monodromy recursion theorem.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices

open Matrix

/-- Channel index for the `d₅ = 3` basis. -/
abbrev Basis5 := Fin 3

/-- Channel index for the `d₆ = 5` basis. -/
abbrev Basis6 := Fin 5

/-- Symbolic entries of the local two-dimensional `B = F R F` block. -/
structure BBlockEntries where
  /-- Upper-left entry. -/
  B00 : ℂ
  /-- Upper-right entry. -/
  B01 : ℂ
  /-- Lower-left entry. -/
  B10 : ℂ
  /-- Lower-right entry. -/
  B11 : ℂ

namespace BBlockEntries

/-- The two-by-two matrix carried by the symbolic block entries. -/
noncomputable def matrix (B : BBlockEntries) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![B.B00, B.B01; B.B10, B.B11]

end BBlockEntries

/-- The `n = 5` matrix for `b₁` in the basis of equation `(6.5)`. -/
noncomputable def pi5_b1 (qNeg4 q3 : ℂ) : Matrix Basis5 Basis5 ℂ :=
  !![q3, 0, 0;
     0, qNeg4, 0;
     0, 0, q3]

/-- The `n = 5` matrix for `b₂` in the basis of equation `(6.5)`. -/
noncomputable def pi5_b2 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis5 Basis5 ℂ :=
  !![q3, 0, 0;
     0, B.B00, B.B01;
     0, B.B10, B.B11]

/-- The `n = 5` matrix for `b₃` in the basis of equation `(6.5)`. -/
noncomputable def pi5_b3 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis5 Basis5 ℂ :=
  !![B.B00, 0, B.B01;
     0, q3, 0;
     B.B10, 0, B.B11]

/-- The `n = 5` matrix for `b₄` in the basis of equation `(6.5)`. -/
noncomputable def pi5_b4 (qNeg4 q3 : ℂ) : Matrix Basis5 Basis5 ℂ :=
  !![qNeg4, 0, 0;
     0, q3, 0;
     0, 0, q3]

/-- The endpoint matrices `π₅(b₁)` and `π₅(b₄)` are diagonal templates. -/
theorem pi5_endpoint_templates (qNeg4 q3 : ℂ) :
    pi5_b1 qNeg4 q3 0 0 = q3 ∧
    pi5_b4 qNeg4 q3 0 0 = qNeg4 := by
  simp [pi5_b1, pi5_b4]

/-- The `b₂` matrix contains the symbolic `B` block on the lower two coordinates. -/
theorem pi5_b2_lower_block (q3 : ℂ) (B : BBlockEntries) :
    pi5_b2 q3 B 1 1 = B.B00 ∧
      pi5_b2 q3 B 1 2 = B.B01 ∧
      pi5_b2 q3 B 2 1 = B.B10 ∧
      pi5_b2 q3 B 2 2 = B.B11 := by
  simp [pi5_b2]

/-- The `b₃` matrix contains the symbolic `B` block on coordinates `0` and `2`. -/
theorem pi5_b3_outer_block (q3 : ℂ) (B : BBlockEntries) :
    pi5_b3 q3 B 0 0 = B.B00 ∧
      pi5_b3 q3 B 0 2 = B.B01 ∧
      pi5_b3 q3 B 2 0 = B.B10 ∧
      pi5_b3 q3 B 2 2 = B.B11 := by
  simp [pi5_b3]

/-- The `n = 6` matrix for `b₁` in the basis of equation `(6.10)`. -/
noncomputable def pi6_b1 (qNeg4 q3 : ℂ) : Matrix Basis6 Basis6 ℂ :=
  !![qNeg4, 0, 0, 0, 0;
     0, q3, 0, 0, 0;
     0, 0, q3, 0, 0;
     0, 0, 0, qNeg4, 0;
     0, 0, 0, 0, q3]

/-- The `n = 6` matrix for `b₂` in the basis of equation `(6.10)`. -/
noncomputable def pi6_b2 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis6 Basis6 ℂ :=
  !![B.B00, B.B01, 0, 0, 0;
     B.B10, B.B11, 0, 0, 0;
     0, 0, q3, 0, 0;
     0, 0, 0, B.B00, B.B01;
     0, 0, 0, B.B10, B.B11]

/-- The `n = 6` matrix for `b₃` in the basis of equation `(6.10)`. -/
noncomputable def pi6_b3 (qNeg4 q3 : ℂ) (B : BBlockEntries) : Matrix Basis6 Basis6 ℂ :=
  !![qNeg4, 0, 0, 0, 0;
     0, q3, 0, 0, 0;
     0, 0, B.B00, 0, B.B01;
     0, 0, 0, q3, 0;
     0, 0, B.B10, 0, B.B11]

/-- The `n = 6` matrix for `b₄` in the basis of equation `(6.10)`. -/
noncomputable def pi6_b4 (q3 : ℂ) (B : BBlockEntries) : Matrix Basis6 Basis6 ℂ :=
  !![B.B00, 0, 0, B.B01, 0;
     0, B.B00, 0, 0, B.B01;
     0, 0, q3, 0, 0;
     B.B10, 0, 0, B.B11, 0;
     0, B.B10, 0, 0, B.B11]

/-- The `n = 6` matrix for `b₅` in the basis of equation `(6.10)`. -/
noncomputable def pi6_b5 (qNeg4 q3 : ℂ) : Matrix Basis6 Basis6 ℂ :=
  !![qNeg4, 0, 0, 0, 0;
     0, qNeg4, 0, 0, 0;
     0, 0, q3, 0, 0;
     0, 0, 0, q3, 0;
     0, 0, 0, 0, q3]

/-- The `b₂` template for `n = 6` repeats the same `B` block twice. -/
theorem pi6_b2_repeated_B_blocks (q3 : ℂ) (B : BBlockEntries) :
    pi6_b2 q3 B 0 0 = B.B00 ∧
      pi6_b2 q3 B 0 1 = B.B01 ∧
      pi6_b2 q3 B 1 0 = B.B10 ∧
      pi6_b2 q3 B 1 1 = B.B11 ∧
      pi6_b2 q3 B 3 3 = B.B00 ∧
      pi6_b2 q3 B 3 4 = B.B01 ∧
      pi6_b2 q3 B 4 3 = B.B10 ∧
      pi6_b2 q3 B 4 4 = B.B11 := by
  simp [pi6_b2]

/-- The `b₅` endpoint template is diagonal with two `q⁻⁴` and three `q³` entries. -/
theorem pi6_b5_diagonal_entries (qNeg4 q3 : ℂ) :
    pi6_b5 qNeg4 q3 0 0 = qNeg4 ∧
      pi6_b5 qNeg4 q3 1 1 = qNeg4 ∧
      pi6_b5 qNeg4 q3 2 2 = q3 ∧
      pi6_b5 qNeg4 q3 3 3 = q3 ∧
      pi6_b5 qNeg4 q3 4 4 = q3 := by
  simp [pi6_b5]

/-- Artin compatibility for the `n = 5` middle relation, from an explicit matrix identity. -/
theorem pi5_middle_artin_from_identity
    (q3 : ℂ) (B : BBlockEntries)
    (h : pi5_b2 q3 B * pi5_b3 q3 B * pi5_b2 q3 B =
      pi5_b3 q3 B * pi5_b2 q3 B * pi5_b3 q3 B) :
    pi5_b2 q3 B * pi5_b3 q3 B * pi5_b2 q3 B =
      pi5_b3 q3 B * pi5_b2 q3 B * pi5_b3 q3 B :=
  h

/-- Artin compatibility for all `n = 6` adjacent pairs, from explicit matrix identities. -/
theorem pi6_adjacent_artin_from_identities
    (qNeg4 q3 : ℂ) (B : BBlockEntries)
    (h12 : pi6_b1 qNeg4 q3 * pi6_b2 q3 B * pi6_b1 qNeg4 q3 =
      pi6_b2 q3 B * pi6_b1 qNeg4 q3 * pi6_b2 q3 B)
    (h23 : pi6_b2 q3 B * pi6_b3 qNeg4 q3 B * pi6_b2 q3 B =
      pi6_b3 qNeg4 q3 B * pi6_b2 q3 B * pi6_b3 qNeg4 q3 B)
    (h34 : pi6_b3 qNeg4 q3 B * pi6_b4 q3 B * pi6_b3 qNeg4 q3 B =
      pi6_b4 q3 B * pi6_b3 qNeg4 q3 B * pi6_b4 q3 B)
    (h45 : pi6_b4 q3 B * pi6_b5 qNeg4 q3 * pi6_b4 q3 B =
      pi6_b5 qNeg4 q3 * pi6_b4 q3 B * pi6_b5 qNeg4 q3) :
    (pi6_b1 qNeg4 q3 * pi6_b2 q3 B * pi6_b1 qNeg4 q3 =
        pi6_b2 q3 B * pi6_b1 qNeg4 q3 * pi6_b2 q3 B) ∧
      (pi6_b2 q3 B * pi6_b3 qNeg4 q3 B * pi6_b2 q3 B =
        pi6_b3 qNeg4 q3 B * pi6_b2 q3 B * pi6_b3 qNeg4 q3 B) ∧
      (pi6_b3 qNeg4 q3 B * pi6_b4 q3 B * pi6_b3 qNeg4 q3 B =
        pi6_b4 q3 B * pi6_b3 qNeg4 q3 B * pi6_b4 q3 B) ∧
      (pi6_b4 q3 B * pi6_b5 qNeg4 q3 * pi6_b4 q3 B =
        pi6_b5 qNeg4 q3 * pi6_b4 q3 B * pi6_b5 qNeg4 q3) :=
  ⟨h12, h23, h34, h45⟩

end InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
