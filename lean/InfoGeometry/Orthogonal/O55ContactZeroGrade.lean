import InfoGeometry.Orthogonal.O55ContactCommonCrosscap

/-!
# Degree-zero structure of the `so(5,5)` contact grading

The zero-grade coordinate generators split into two commuting families:

* `E₋ ∧ E₊`, with the matrix-unit bracket of a `gl(2)`-shaped action;
* `Λ²W`, with the rank-two orthogonal bracket of the split middle form.

The file proves the generator brackets and their actions on degree `±1`.
It does not install an abstract `gl(2) ⊕ so(3,3)` isomorphism before a full
basis-level equivalence is constructed.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Antisymmetry of rank-two generators. -/
theorem splitRankTwo_swap (u v : Vector55) :
    splitRankTwo v u = -splitRankTwo u v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  simp [splitRankTwo, splitRankTwoEnd]

/-- Outer degree-zero generator. -/
def outerZeroGenerator (a b : Outer2) : O55Lie :=
  splitRankTwo (embedOuterMinus a) (embedOuterPlus b)

/-- Middle degree-zero generator. -/
def middleZeroGenerator (w z : Middle6) : O55Lie :=
  splitRankTwo (embedMiddle w) (embedMiddle z)

def negativeOneGenerator (a : Outer2) (w : Middle6) : O55Lie :=
  splitRankTwo (embedOuterMinus a) (embedMiddle w)

def positiveOneGenerator (a : Outer2) (w : Middle6) : O55Lie :=
  splitRankTwo (embedMiddle w) (embedOuterPlus a)

/-- Both zero-grade families are genuinely homogeneous. -/
theorem zero_generator_grade_packet
    (a b : Outer2) (w z : Middle6) :
    outerZeroGenerator a b ∈ realContactGradeSpace 0 ∧
      middleZeroGenerator w z ∈ realContactGradeSpace 0 := by
  rcases embedded_weight_packet with ⟨hm, h0, hp⟩
  exact ⟨by
      simpa [outerZeroGenerator] using
        splitRankTwo_grade (hm a) (hp b),
    by
      simpa [middleZeroGenerator] using
        splitRankTwo_grade (h0 w) (h0 z)⟩

/-- The outer and middle zero-grade families commute. -/
theorem outerZero_bracket_middleZero
    (a b : Outer2) (w z : Middle6) :
    ⁅outerZeroGenerator a b, middleZeroGenerator w z⁆ = 0 := by
  unfold outerZeroGenerator middleZeroGenerator
  rw [splitRankTwo_bracket]
  simp

/-- Matrix-unit bracket for the outer zero-grade family. -/
theorem outerZero_bracket
    (a b c d : Outer2) :
    ⁅outerZeroGenerator a b, outerZeroGenerator c d⁆ =
      outerPairing b c • outerZeroGenerator a d -
        outerPairing a d • outerZeroGenerator c b := by
  unfold outerZeroGenerator
  rw [splitRankTwo_bracket]
  simp only [pairing_outerPlus_outerMinus,
    pairing_outerMinus_outerMinus, pairing_outerPlus_outerPlus,
    pairing_outerMinus_outerPlus, zero_smul, sub_zero, add_zero]
  have hswap := splitRankTwo_swap (embedOuterPlus b) (embedOuterMinus c)
  rw [hswap]
  module

/-- Orthogonal rank-two bracket for the middle zero-grade family. -/
theorem middleZero_bracket
    (u v w z : Middle6) :
    ⁅middleZeroGenerator u v, middleZeroGenerator w z⁆ =
      middlePairing v w • middleZeroGenerator u z -
      middlePairing u w • middleZeroGenerator v z -
      middlePairing v z • middleZeroGenerator u w +
      middlePairing u z • middleZeroGenerator v w := by
  unfold middleZeroGenerator
  simpa using
    splitRankTwo_bracket (embedMiddle u) (embedMiddle v)
      (embedMiddle w) (embedMiddle z)

/-- Outer zero-grade action on degree `-1`. -/
theorem outerZero_action_negativeOne
    (a b c : Outer2) (w : Middle6) :
    ⁅outerZeroGenerator a b, negativeOneGenerator c w⁆ =
      outerPairing b c • negativeOneGenerator a w := by
  unfold outerZeroGenerator negativeOneGenerator
  rw [splitRankTwo_bracket]
  simp

/-- Outer zero-grade action on degree `+1`. -/
theorem outerZero_action_positiveOne
    (a b c : Outer2) (w : Middle6) :
    ⁅outerZeroGenerator a b, positiveOneGenerator c w⁆ =
      -(outerPairing a c) • positiveOneGenerator b w := by
  unfold outerZeroGenerator positiveOneGenerator
  rw [splitRankTwo_bracket]
  simp only [pairing_outerPlus_outerPlus,
    pairing_outerMinus_outerPlus, pairing_outerPlus_middle,
    pairing_outerMinus_middle, zero_smul, sub_zero, add_zero]
  rw [splitRankTwo_swap]
  module

/-- Middle zero-grade action on degree `-1`. -/
theorem middleZero_action_negativeOne
    (u v w : Middle6) (a : Outer2) :
    ⁅middleZeroGenerator u v, negativeOneGenerator a w⁆ =
      middlePairing v w • negativeOneGenerator a u -
        middlePairing u w • negativeOneGenerator a v := by
  unfold middleZeroGenerator negativeOneGenerator
  rw [splitRankTwo_bracket]
  have hvm : splitPairing (embedMiddle v) (embedOuterMinus a) = 0 := by
    rw [splitPairing_comm]
    simp
  have hum : splitPairing (embedMiddle u) (embedOuterMinus a) = 0 := by
    rw [splitPairing_comm]
    simp
  rw [hvm, hum]
  rw [pairing_middle_middle, pairing_middle_middle]
  simp only [zero_smul, sub_zero, zero_sub]
  rw [splitRankTwo_swap (embedOuterMinus a) (embedMiddle u),
    splitRankTwo_swap (embedOuterMinus a) (embedMiddle v)]
  module

/-- Middle zero-grade action on degree `+1`. -/
theorem middleZero_action_positiveOne
    (u v w : Middle6) (a : Outer2) :
    ⁅middleZeroGenerator u v, positiveOneGenerator a w⁆ =
      middlePairing v w • positiveOneGenerator a u -
        middlePairing u w • positiveOneGenerator a v := by
  unfold middleZeroGenerator positiveOneGenerator
  rw [splitRankTwo_bracket]
  have hvm : splitPairing (embedMiddle v) (embedOuterPlus a) = 0 := by
    rw [splitPairing_comm]
    simp
  have hum : splitPairing (embedMiddle u) (embedOuterPlus a) = 0 := by
    rw [splitPairing_comm]
    simp
  rw [hvm, hum]
  rw [pairing_middle_middle, pairing_middle_middle]
  simp only [zero_smul, sub_zero, zero_sub]
  simp

/-- The degree-zero structural packet. -/
theorem zero_grade_structure_packet
    (a b c d : Outer2) (u v w z : Middle6) :
    ⁅outerZeroGenerator a b, middleZeroGenerator u v⁆ = 0 ∧
      ⁅outerZeroGenerator a b, outerZeroGenerator c d⁆ =
        outerPairing b c • outerZeroGenerator a d -
          outerPairing a d • outerZeroGenerator c b ∧
      ⁅middleZeroGenerator u v, middleZeroGenerator w z⁆ =
        middlePairing v w • middleZeroGenerator u z -
        middlePairing u w • middleZeroGenerator v z -
        middlePairing v z • middleZeroGenerator u w +
        middlePairing u z • middleZeroGenerator v w := by
  exact ⟨outerZero_bracket_middleZero a b u v,
    outerZero_bracket a b c d,
    middleZero_bracket u v w z⟩

end InfoGeometry.Orthogonal.O55Contact
