import InfoGeometry.Orthogonal.O55ContactCARCCRRepresentation

/-!
# Coordinate-generator census for the `so(5,5)` contact grading

The `2 + 6 + 2` vector decomposition gives coordinate rank-two generators in
the pattern

`1, 12, 19, 12, 1`.

The theorem below is an exact finite index count and every label is mapped to
a generator in the corresponding homogeneous submodule.  The file does not
rename this count as a linear-basis theorem; linear independence is a separate
statement.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Standard basis of the outer two-space. -/
def outerBasis (i : Fin 2) : Outer2 :=
  fun j => if j = i then 1 else 0

/-- Standard basis of the middle six-space. -/
def middleBasis (i : Fin 6) : Middle6 :=
  fun j => if j = i then 1 else 0

/-- Enumeration of the fifteen unordered coordinate pairs in six dimensions. -/
def middlePair : Fin 15 → Fin 6 × Fin 6 :=
  ![((0 : Fin 6), (1 : Fin 6)),
    ((0 : Fin 6), (2 : Fin 6)),
    ((0 : Fin 6), (3 : Fin 6)),
    ((0 : Fin 6), (4 : Fin 6)),
    ((0 : Fin 6), (5 : Fin 6)),
    ((1 : Fin 6), (2 : Fin 6)),
    ((1 : Fin 6), (3 : Fin 6)),
    ((1 : Fin 6), (4 : Fin 6)),
    ((1 : Fin 6), (5 : Fin 6)),
    ((2 : Fin 6), (3 : Fin 6)),
    ((2 : Fin 6), (4 : Fin 6)),
    ((2 : Fin 6), (5 : Fin 6)),
    ((3 : Fin 6), (4 : Fin 6)),
    ((3 : Fin 6), (5 : Fin 6)),
    ((4 : Fin 6), (5 : Fin 6))]

@[simp] theorem middlePair_ordered (i : Fin 15) :
    (middlePair i).1 < (middlePair i).2 := by
  fin_cases i <;> decide

/-- Finite coordinate-generator labels. -/
inductive ContactGeneratorLabel
  | minusTwo
  | minusOne (outer : Fin 2) (middle : Fin 6)
  | zeroOuter (target source : Fin 2)
  | zeroMiddle (pair : Fin 15)
  | plusOne (outer : Fin 2) (middle : Fin 6)
  | plusTwo
  deriving DecidableEq, Fintype, Repr

namespace ContactGeneratorLabel

/-- Contact degree of a coordinate-generator label. -/
def degree : ContactGeneratorLabel → ℤ
  | minusTwo => -2
  | minusOne _ _ => -1
  | zeroOuter _ _ => 0
  | zeroMiddle _ => 0
  | plusOne _ _ => 1
  | plusTwo => 2

/-- Concrete rank-two generator attached to a label. -/
def generator : ContactGeneratorLabel → O55Lie
  | minusTwo => gradeMinusTwo
  | minusOne i j =>
      negativeOneGenerator (outerBasis i) (middleBasis j)
  | zeroOuter i j =>
      splitRankTwo
        (embedOuterMinus (outerBasis i))
        (embedOuterPlus (outerBasis j))
  | zeroMiddle p =>
      splitRankTwo
        (embedMiddle (middleBasis (middlePair p).1))
        (embedMiddle (middleBasis (middlePair p).2))
  | plusOne i j =>
      positiveOneGenerator (outerBasis i) (middleBasis j)
  | plusTwo => gradePlusTwo

/-- Every coordinate generator lies in its labeled grade. -/
theorem generator_mem_grade (g : ContactGeneratorLabel) :
    g.generator ∈ contactGradeSpace g.degree := by
  rcases embedded_weight_packet with ⟨hm, h0, hp⟩
  cases g with
  | minusTwo => exact five_grades_inhabited.1
  | minusOne i j =>
      simpa [generator, degree, negativeOneGenerator] using
        splitRankTwo_grade (hm (outerBasis i)) (h0 (middleBasis j))
  | zeroOuter i j =>
      simpa [generator, degree] using
        splitRankTwo_grade (hm (outerBasis i)) (hp (outerBasis j))
  | zeroMiddle p =>
      simpa [generator, degree] using
        splitRankTwo_grade
          (h0 (middleBasis (middlePair p).1))
          (h0 (middleBasis (middlePair p).2))
  | plusOne i j =>
      simpa [generator, degree, positiveOneGenerator, add_comm] using
        splitRankTwo_grade (hp (outerBasis i)) (h0 (middleBasis j))
  | plusTwo => exact five_grades_inhabited.2.2.2.2

end ContactGeneratorLabel

/-- Labels in one contact lane. -/
abbrev ContactLaneLabel (k : ℤ) :=
  {g : ContactGeneratorLabel // g.degree = k}

/-- Total coordinate-generator count. -/
theorem contact_generator_label_count :
    Fintype.card ContactGeneratorLabel = 45 := by
  native_decide

/-- Exact contact-lane count pattern. -/
theorem contact_lane_label_counts :
    Fintype.card (ContactLaneLabel (-2)) = 1 ∧
      Fintype.card (ContactLaneLabel (-1)) = 12 ∧
      Fintype.card (ContactLaneLabel 0) = 19 ∧
      Fintype.card (ContactLaneLabel 1) = 12 ∧
      Fintype.card (ContactLaneLabel 2) = 1 := by
  native_decide

/-- The lane counts sum to the orthogonal-generator count. -/
theorem contact_lane_counts_sum :
    1 + 12 + 19 + 12 + 1 = Nat.choose 10 2 := by
  norm_num [Nat.choose]

/-- Coordinate count agrees with the repository's existing `O(5,5)` count. -/
theorem contact_generator_count_agreement :
    Fintype.card ContactGeneratorLabel =
      PinO55GlideReflection.o55GeneratorCount := by
  rw [contact_generator_label_count]
  exact PinO55GlideReflection.o55_glide_counts.2.1.symm

/-- Count and typed-grade packet. -/
theorem contact_generator_census_packet :
    Fintype.card ContactGeneratorLabel = 45 ∧
      Fintype.card (ContactLaneLabel (-2)) = 1 ∧
      Fintype.card (ContactLaneLabel (-1)) = 12 ∧
      Fintype.card (ContactLaneLabel 0) = 19 ∧
      Fintype.card (ContactLaneLabel 1) = 12 ∧
      Fintype.card (ContactLaneLabel 2) = 1 ∧
      (∀ g : ContactGeneratorLabel,
        g.generator ∈ contactGradeSpace g.degree) := by
  rcases contact_lane_label_counts with ⟨h₂m, h₁m, h₀, h₁, h₂⟩
  exact ⟨contact_generator_label_count, h₂m, h₁m, h₀, h₁, h₂,
    ContactGeneratorLabel.generator_mem_grade⟩

end InfoGeometry.Orthogonal.O55Contact
