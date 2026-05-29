import InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices

/-!
# InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonPaperBridge

Paper-facing bridge for the sparse `n = 7` and `n = 8` Fibonacci braid
templates.

The owned sparse low-anyon file records the explicit finite matrix structure
shown in Section 6 of the paper.  This bridge exposes those templates in a
finite theorem-facing form:

* basis sizes `d₇ = 8` and `d₈ = 13`;
* diagonal phase vectors for the endpoint generators;
* representative `B`-block placements for the interior generators.

No conformal blocks.
No analytic continuation.
No claim that these templates are derived from hypergeometric formulas here.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonPaperBridge

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices

/-- The `n = 7` basis has eight channels. -/
theorem sectionSix_basis7_card :
    Fintype.card Basis7 = 8 := by
  rfl

/-- The `n = 8` basis has thirteen channels. -/
theorem sectionSix_basis8_card :
    Fintype.card Basis8 = 13 := by
  rfl

/-- The `n = 7` left endpoint braid has the expected phase pattern. -/
theorem sectionSix_pi7_b1_phase (qNeg4 q3 : ℂ) :
    pi7_b1_phase qNeg4 q3 =
      ![q3, qNeg4, q3, qNeg4, q3, q3, qNeg4, q3] :=
  rfl

/-- The `n = 7` right endpoint braid has the expected phase pattern. -/
theorem sectionSix_pi7_b6_phase (qNeg4 q3 : ℂ) :
    pi7_b6_phase qNeg4 q3 =
      ![qNeg4, qNeg4, qNeg4, q3, q3, q3, q3, q3] :=
  rfl

/-- The `n = 8` left endpoint braid has the expected phase pattern. -/
theorem sectionSix_pi8_b1_phase (qNeg4 q3 : ℂ) :
    pi8_b1_phase qNeg4 q3 =
      ![qNeg4, q3, q3, qNeg4, q3, q3, qNeg4, q3, qNeg4, q3, q3, qNeg4, q3] :=
  rfl

/-- The `n = 8` right endpoint braid has the expected phase pattern. -/
theorem sectionSix_pi8_b7_phase (qNeg4 q3 : ℂ) :
    pi8_b7_phase qNeg4 q3 =
      ![qNeg4, qNeg4, qNeg4, qNeg4, qNeg4, q3, q3, q3, q3, q3, q3, q3, q3] :=
  rfl

/-- The first interior `n = 7` braid has a `B` block on coordinates `(1, 2)`. -/
theorem sectionSix_pi7_b2_first_block
    (q3 : ℂ)
    (B : InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices.BBlockEntries) :
    pi7_b2 q3 B 1 1 = B.B00 ∧ pi7_b2 q3 B 1 2 = B.B01 ∧
      pi7_b2 q3 B 2 1 = B.B10 ∧ pi7_b2 q3 B 2 2 = B.B11 :=
  InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices.pi7_b2_first_block q3 B

/-- The `n = 8` generator `b₆` has a `B` block on coordinates `(0, 8)`. -/
theorem sectionSix_pi8_b6_first_block
    (q3 : ℂ)
    (B : InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices.BBlockEntries) :
    pi8_b6 q3 B 0 0 = B.B00 ∧ pi8_b6 q3 B 0 8 = B.B01 ∧
      pi8_b6 q3 B 8 0 = B.B10 ∧ pi8_b6 q3 B 8 8 = B.B11 :=
  InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonMatrices.pi8_b6_first_block q3 B

end InfoGeometry.Canonical.FiniteFibonacciSparseLowAnyonPaperBridge
