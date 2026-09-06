import InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices

/-!
# InfoGeometry.Canonical.FiniteFibonacciLowAnyonPaperBridge

Paper-facing finite bridge for the low-anyon section of the Fibonacci braid
templates.

The owned repository surface already contains finite symbolic templates for the
first effective cases listed in Section 6:

* `n = 5`, with basis size `d₅ = 3`;
* `n = 6`, with basis size `d₆ = 5`.

This bridge exposes those templates in paper-facing theorem form.  It does not
claim the explicit `n = 7` and `n = 8` tables from the paper, because the owner
surface does not yet provide those matrices.

No conformal blocks.
No analytic continuation.
No `n = 7` or `n = 8` matrix claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciLowAnyonPaperBridge

open FiniteFibonacciLowAnyonMatrices

/-- The `n = 5` basis has three channels. -/
theorem sectionSix_basis5_card :
    Fintype.card Basis5 = 3 := by
  rfl

/-- The `n = 6` basis has five channels. -/
theorem sectionSix_basis6_card :
    Fintype.card Basis6 = 5 := by
  rfl

/-- The `n = 5` endpoint braids are diagonal templates. -/
theorem sectionSix_n5_endpoint_templates (qNeg4 q3 : ℂ) :
    pi5_b1 qNeg4 q3 0 0 = q3 ∧
      pi5_b4 qNeg4 q3 0 0 = qNeg4 :=
  pi5_endpoint_templates qNeg4 q3

/-- The `n = 5` middle braid contains the symbolic `B` block in the lower-right sector. -/
theorem sectionSix_n5_b2_lower_block (q3 : ℂ) (B : BBlockEntries) :
    pi5_b2 q3 B 1 1 = BBlockEntries.B00 B ∧
      pi5_b2 q3 B 1 2 = BBlockEntries.B01 B ∧
      pi5_b2 q3 B 2 1 = BBlockEntries.B10 B ∧
      pi5_b2 q3 B 2 2 = BBlockEntries.B11 B :=
  pi5_b2_lower_block q3 B

/-- The `n = 5` outer braid contains the same symbolic `B` block on coordinates `0` and `2`. -/
theorem sectionSix_n5_b3_outer_block (q3 : ℂ) (B : BBlockEntries) :
    pi5_b3 q3 B 0 0 = BBlockEntries.B00 B ∧
      pi5_b3 q3 B 0 2 = BBlockEntries.B01 B ∧
      pi5_b3 q3 B 2 0 = BBlockEntries.B10 B ∧
      pi5_b3 q3 B 2 2 = BBlockEntries.B11 B :=
  pi5_b3_outer_block q3 B

/-
theorem sectionSix_n5_middle_artin_from_identity
    (q3 : ℂ) (B : BBlockEntries)
    (h : pi5_b2 q3 B * pi5_b3 q3 B * pi5_b2 q3 B =
      pi5_b3 q3 B * pi5_b2 q3 B * pi5_b3 q3 B) :
    pi5_b2 q3 B * pi5_b3 q3 B * pi5_b2 q3 B =
      pi5_b3 q3 B * pi5_b2 q3 B * pi5_b3 q3 B :=
  pi5_middle_artin_from_identity q3 B h
-/

/-- The repo-owned `n = 6` endpoint braid templates are the next finite owner surface exposed here. -/
theorem sectionSix_n6_endpoint_templates (qNeg4 q3 : ℂ) :
    pi6_b1 qNeg4 q3 0 0 = qNeg4 ∧
      pi6_b5 qNeg4 q3 4 4 = q3 :=
  ⟨by simp [pi6_b1], by simp [pi6_b5]⟩

/-- The `n = 6` middle braid repeats the same `B` block twice. -/
theorem sectionSix_n6_repeated_B_blocks (q3 : ℂ) (B : BBlockEntries) :
    pi6_b2 q3 B 0 0 = BBlockEntries.B00 B ∧
      pi6_b2 q3 B 0 1 = BBlockEntries.B01 B ∧
      pi6_b2 q3 B 1 0 = BBlockEntries.B10 B ∧
      pi6_b2 q3 B 1 1 = BBlockEntries.B11 B ∧
      pi6_b2 q3 B 3 3 = BBlockEntries.B00 B ∧
      pi6_b2 q3 B 3 4 = BBlockEntries.B01 B ∧
      pi6_b2 q3 B 4 3 = BBlockEntries.B10 B ∧
      pi6_b2 q3 B 4 4 = BBlockEntries.B11 B :=
  pi6_b2_repeated_B_blocks q3 B

/-- The `n = 6` endpoint braid `b₅` is diagonal with two `q⁻⁴` and three `q³` entries. -/
theorem sectionSix_n6_b5_diagonal_entries (qNeg4 q3 : ℂ) :
    pi6_b5 qNeg4 q3 0 0 = qNeg4 ∧
      pi6_b5 qNeg4 q3 1 1 = qNeg4 ∧
      pi6_b5 qNeg4 q3 2 2 = q3 ∧
      pi6_b5 qNeg4 q3 3 3 = q3 ∧
      pi6_b5 qNeg4 q3 4 4 = q3 :=
  pi6_b5_diagonal_entries qNeg4 q3

/-
theorem sectionSix_n6_adjacent_artin_from_identities
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
  pi6_adjacent_artin_from_identities qNeg4 q3 B h12 h23 h34 h45
-/

end InfoGeometry.Canonical.FiniteFibonacciLowAnyonPaperBridge
