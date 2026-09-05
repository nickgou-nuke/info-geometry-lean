import InfoGeometry.Orthogonal.O55ContactMultiGrading

/-!
# Heisenberg structure of the `so(5,5)` contact grading

Write the split carrier as `E₋ ⊕ W ⊕ E₊`, with dimensions `2 + 6 + 2`.
The degree `-1` and `+1` generators are `E₋ ∧ W` and `E₊ ∧ W`.
Their same-sign brackets land in the one-dimensional extreme lanes, which
centralize the corresponding nilpotent radicals.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

abbrev Outer2 := Fin 2 → ℝ
abbrev Middle6 := Fin 6 → ℝ

def outerPairing (a b : Outer2) : ℝ := a 0 * b 0 + a 1 * b 1

def outerArea (a b : Outer2) : ℝ := a 0 * b 1 - a 1 * b 0

def middlePairing (w z : Middle6) : ℝ :=
  w 0 * z 0 + w 1 * z 1 + w 2 * z 2 -
    w 3 * z 3 - w 4 * z 4 - w 5 * z 5

def embedOuterMinus (a : Outer2) : Vector55 :=
  ![a 0, a 1, 0, 0, 0, 0, 0, 0, 0, 0]

def embedMiddle (w : Middle6) : Vector55 :=
  ![0, 0, w 0, w 1, w 2, w 3, w 4, w 5, 0, 0]

def embedOuterPlus (a : Outer2) : Vector55 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, a 0, a 1]

@[simp] theorem pairing_outerMinus_outerMinus (a b : Outer2) :
    splitPairing (embedOuterMinus a) (embedOuterMinus b) = 0 := by
  simp [splitPairing, embedOuterMinus]

@[simp] theorem pairing_outerPlus_outerPlus (a b : Outer2) :
    splitPairing (embedOuterPlus a) (embedOuterPlus b) = 0 := by
  simp [splitPairing, embedOuterPlus]

@[simp] theorem pairing_outerMinus_outerPlus (a b : Outer2) :
    splitPairing (embedOuterMinus a) (embedOuterPlus b) =
      outerPairing a b := by
  simp [splitPairing, embedOuterMinus, embedOuterPlus, outerPairing]

@[simp] theorem pairing_outerPlus_outerMinus (a b : Outer2) :
    splitPairing (embedOuterPlus a) (embedOuterMinus b) =
      outerPairing a b := by
  simp [splitPairing, embedOuterMinus, embedOuterPlus, outerPairing]

@[simp] theorem pairing_middle_middle (w z : Middle6) :
    splitPairing (embedMiddle w) (embedMiddle z) = middlePairing w z := by
  simp [splitPairing, embedMiddle, middlePairing]

@[simp] theorem pairing_outerMinus_middle (a : Outer2) (w : Middle6) :
    splitPairing (embedOuterMinus a) (embedMiddle w) = 0 := by
  simp [splitPairing, embedOuterMinus, embedMiddle]

@[simp] theorem pairing_middle_outerMinus (w : Middle6) (a : Outer2) :
    splitPairing (embedMiddle w) (embedOuterMinus a) = 0 := by
  simp [splitPairing, embedOuterMinus, embedMiddle]

@[simp] theorem pairing_outerPlus_middle (a : Outer2) (w : Middle6) :
    splitPairing (embedOuterPlus a) (embedMiddle w) = 0 := by
  simp [splitPairing, embedOuterPlus, embedMiddle]

@[simp] theorem pairing_middle_outerPlus (w : Middle6) (a : Outer2) :
    splitPairing (embedMiddle w) (embedOuterPlus a) = 0 := by
  simp [splitPairing, embedOuterPlus, embedMiddle]

/-- Embedded sectors have Euler weights `-1,0,+1`. -/
theorem embedded_weight_packet :
    (∀ a : Outer2, IsVectorWeight (-1) (embedOuterMinus a)) ∧
      (∀ w : Middle6, IsVectorWeight 0 (embedMiddle w)) ∧
      (∀ a : Outer2, IsVectorWeight 1 (embedOuterPlus a)) := by
  constructor
  · intro a
    funext i
    fin_cases i <;>
      simp [IsVectorWeight, contactEulerEnd, contactWeightR,
        contactWeight, embedOuterMinus]
  constructor
  · intro w
    funext i
    fin_cases i <;>
      simp [IsVectorWeight, contactEulerEnd, contactWeightR,
        contactWeight, embedMiddle]
  · intro a
    funext i
    fin_cases i <;>
      simp [IsVectorWeight, contactEulerEnd, contactWeightR,
        contactWeight, embedOuterPlus]

/-- Universal commutator identity for split rank-two generators. -/
theorem splitRankTwoEnd_commutator (u v w z : Vector55) :
    endCommutator (splitRankTwoEnd u v) (splitRankTwoEnd w z) =
      splitPairing v w • splitRankTwoEnd u z -
      splitPairing u w • splitRankTwoEnd v z -
      splitPairing v z • splitRankTwoEnd u w +
      splitPairing u z • splitRankTwoEnd v w := by
  apply LinearMap.ext
  intro x
  simp only [endCommutator_apply, splitRankTwoEnd_apply,
    splitPairing_sub_right, splitPairing_smul_right,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_sub, smul_smul]
  rw [splitPairing_comm z u, splitPairing_comm z v,
    splitPairing_comm w u, splitPairing_comm w v]
  module

/-- Lie-subalgebra form of the rank-two commutator identity. -/
theorem splitRankTwo_bracket (u v w z : Vector55) :
    ⁅splitRankTwo u v, splitRankTwo w z⁆ =
      splitPairing v w • splitRankTwo u z -
      splitPairing u w • splitRankTwo v z -
      splitPairing v z • splitRankTwo u w +
      splitPairing u z • splitRankTwo v w := by
  apply Subtype.ext
  exact splitRankTwoEnd_commutator u v w z

def negativeTwoGenerator (a b : Outer2) : O55Lie :=
  splitRankTwo (embedOuterMinus a) (embedOuterMinus b)

def negativeOneGenerator (a : Outer2) (w : Middle6) : O55Lie :=
  splitRankTwo (embedOuterMinus a) (embedMiddle w)

def positiveOneGenerator (a : Outer2) (w : Middle6) : O55Lie :=
  splitRankTwo (embedOuterPlus a) (embedMiddle w)

def positiveTwoGenerator (a b : Outer2) : O55Lie :=
  splitRankTwo (embedOuterPlus a) (embedOuterPlus b)

theorem contact_generator_grade_packet
    (a b : Outer2) (w : Middle6) :
    negativeTwoGenerator a b ∈ contactGradeSpace (-2) ∧
      negativeOneGenerator a w ∈ contactGradeSpace (-1) ∧
      positiveOneGenerator a w ∈ contactGradeSpace 1 ∧
      positiveTwoGenerator a b ∈ contactGradeSpace 2 := by
  rcases embedded_weight_packet with ⟨hm, h0, hp⟩
  exact ⟨by
      simpa [negativeTwoGenerator] using splitRankTwo_grade (hm a) (hm b),
    by
      simpa [negativeOneGenerator] using splitRankTwo_grade (hm a) (h0 w),
    by
      simpa [positiveOneGenerator, add_comm] using
        splitRankTwo_grade (hp a) (h0 w),
    by
      simpa [positiveTwoGenerator] using splitRankTwo_grade (hp a) (hp b)⟩

theorem negativeOne_bracket
    (a b : Outer2) (w z : Middle6) :
    ⁅negativeOneGenerator a w, negativeOneGenerator b z⁆ =
      -(middlePairing w z) • negativeTwoGenerator a b := by
  unfold negativeOneGenerator negativeTwoGenerator
  rw [splitRankTwo_bracket]
  simp

theorem positiveOne_bracket
    (a b : Outer2) (w z : Middle6) :
    ⁅positiveOneGenerator a w, positiveOneGenerator b z⁆ =
      -(middlePairing w z) • positiveTwoGenerator a b := by
  unfold positiveOneGenerator positiveTwoGenerator
  rw [splitRankTwo_bracket]
  simp

theorem negativeTwo_bracket_negativeOne
    (a b c : Outer2) (w : Middle6) :
    ⁅negativeTwoGenerator a b, negativeOneGenerator c w⁆ = 0 := by
  unfold negativeTwoGenerator negativeOneGenerator
  rw [splitRankTwo_bracket]
  simp

theorem positiveTwo_bracket_positiveOne
    (a b c : Outer2) (w : Middle6) :
    ⁅positiveTwoGenerator a b, positiveOneGenerator c w⁆ = 0 := by
  unfold positiveTwoGenerator positiveOneGenerator
  rw [splitRankTwo_bracket]
  simp

theorem negativeTwo_bracket_negativeTwo
    (a b c d : Outer2) :
    ⁅negativeTwoGenerator a b, negativeTwoGenerator c d⁆ = 0 := by
  unfold negativeTwoGenerator
  rw [splitRankTwo_bracket]
  simp

theorem positiveTwo_bracket_positiveTwo
    (a b c d : Outer2) :
    ⁅positiveTwoGenerator a b, positiveTwoGenerator c d⁆ = 0 := by
  unfold positiveTwoGenerator
  rw [splitRankTwo_bracket]
  simp

theorem negativeTwo_eq_area_smul (a b : Outer2) :
    negativeTwoGenerator a b = outerArea a b • gradeMinusTwo := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [negativeTwoGenerator, outerArea, gradeMinusTwo,
      splitRankTwo, splitRankTwoEnd, embedOuterMinus,
      splitPairing, coordinateVector] <;> ring

theorem positiveTwo_eq_area_smul (a b : Outer2) :
    positiveTwoGenerator a b = outerArea a b • gradePlusTwo := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [positiveTwoGenerator, outerArea, gradePlusTwo,
      splitRankTwo, splitRankTwoEnd, embedOuterPlus,
      splitPairing, coordinateVector] <;> ring

theorem negativeOne_bracket_scalar
    (a b : Outer2) (w z : Middle6) :
    ⁅negativeOneGenerator a w, negativeOneGenerator b z⁆ =
      (-(middlePairing w z * outerArea a b)) • gradeMinusTwo := by
  rw [negativeOne_bracket, negativeTwo_eq_area_smul]
  simp [smul_smul]
  ring

theorem positiveOne_bracket_scalar
    (a b : Outer2) (w z : Middle6) :
    ⁅positiveOneGenerator a w, positiveOneGenerator b z⁆ =
      (-(middlePairing w z * outerArea a b)) • gradePlusTwo := by
  rw [positiveOne_bracket, positiveTwo_eq_area_smul]
  simp [smul_smul]
  ring

theorem mixed_one_bracket_grade_zero
    (a b : Outer2) (w z : Middle6) :
    ⁅negativeOneGenerator a w, positiveOneGenerator b z⁆ ∈
      contactGradeSpace 0 := by
  rcases embedded_weight_packet with ⟨hm, h0, hp⟩
  exact contactGrade_bracket
    (by simpa [negativeOneGenerator] using splitRankTwo_grade (hm a) (h0 w))
    (by simpa [positiveOneGenerator, add_comm] using
      splitRankTwo_grade (hp b) (h0 z))

theorem negative_heisenberg_packet
    (a b c d : Outer2) (w z : Middle6) :
    ⁅negativeOneGenerator a w, negativeOneGenerator b z⁆ =
        (-(middlePairing w z * outerArea a b)) • gradeMinusTwo ∧
      ⁅negativeTwoGenerator a b, negativeOneGenerator c w⁆ = 0 ∧
      ⁅negativeTwoGenerator a b, negativeTwoGenerator c d⁆ = 0 := by
  exact ⟨negativeOne_bracket_scalar a b w z,
    negativeTwo_bracket_negativeOne a b c w,
    negativeTwo_bracket_negativeTwo a b c d⟩

theorem positive_heisenberg_packet
    (a b c d : Outer2) (w z : Middle6) :
    ⁅positiveOneGenerator a w, positiveOneGenerator b z⁆ =
        (-(middlePairing w z * outerArea a b)) • gradePlusTwo ∧
      ⁅positiveTwoGenerator a b, positiveOneGenerator c w⁆ = 0 ∧
      ⁅positiveTwoGenerator a b, positiveTwoGenerator c d⁆ = 0 := by
  exact ⟨positiveOne_bracket_scalar a b w z,
    positiveTwo_bracket_positiveOne a b c w,
    positiveTwo_bracket_positiveTwo a b c d⟩

end InfoGeometry.Orthogonal.O55Contact
