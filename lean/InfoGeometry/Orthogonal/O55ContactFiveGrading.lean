import InfoGeometry.Orthogonal.O55ContactCarrier

/-!
# Native contact five-grading of `so(5,5)`

The Euler element has vector weights `-1,0,+1`.  Its adjoint eigenspaces have
contact degrees `-2,-1,0,+1,+2`.  The homogeneous spaces are native real
submodules, and their bracket-addition law is proved inside the associative
endomorphism representation.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Commutator in the associative endomorphism algebra. -/
def endCommutator (A B : End55) : End55 := A * B - B * A

@[simp] theorem endCommutator_apply (A B : End55) (x : Vector55) :
    endCommutator A B x = A (B x) - B (A x) := rfl

/-- Homogeneity for the contact Euler action. -/
def IsContactGrade (k : ℤ) (A : O55Lie) : Prop :=
  endCommutator contactEulerEnd (A : End55) =
    (k : ℝ) • (A : End55)

/-- Native homogeneous submodule of contact degree `k`. -/
def contactGradeSpace (k : ℤ) : Submodule ℝ O55Lie where
  carrier := {A | IsContactGrade k A}
  zero_mem' := by simp [IsContactGrade, endCommutator]
  add_mem' := by
    intro A B hA hB
    unfold IsContactGrade at hA hB ⊢
    change endCommutator contactEulerEnd
        ((A : End55) + (B : End55)) =
      (k : ℝ) • ((A : End55) + (B : End55))
    simp only [endCommutator, mul_add, add_mul]
    rw [hA, hB]
    module
  smul_mem' := by
    intro c A hA
    unfold IsContactGrade at hA ⊢
    change endCommutator contactEulerEnd (c • (A : End55)) =
      (k : ℝ) • (c • (A : End55))
    simp only [endCommutator, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc]
    rw [hA]
    module

@[simp] theorem mem_contactGradeSpace_iff (k : ℤ) (A : O55Lie) :
    A ∈ contactGradeSpace k ↔ IsContactGrade k A := Iff.rfl

/-- The Euler element has degree zero. -/
theorem contactEuler_mem_grade_zero :
    contactEuler ∈ contactGradeSpace 0 := by
  change endCommutator contactEulerEnd contactEulerEnd =
    (0 : ℝ) • contactEulerEnd
  simp [endCommutator]

/-- The adjoint action of the Euler operator is a derivation. -/
theorem endCommutator_derivation (A B : End55) :
    endCommutator contactEulerEnd (endCommutator A B) =
      endCommutator (endCommutator contactEulerEnd A) B +
        endCommutator A (endCommutator contactEulerEnd B) := by
  unfold endCommutator
  noncomm_ring

/-- Contact degrees add under the native Lie bracket. -/
theorem contactGrade_bracket
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ contactGradeSpace k)
    (hB : B ∈ contactGradeSpace l) :
    ⁅A, B⁆ ∈ contactGradeSpace (k + l) := by
  unfold contactGradeSpace IsContactGrade at hA hB ⊢
  change endCommutator contactEulerEnd
      (endCommutator (A : End55) (B : End55)) =
    ((k + l : ℤ) : ℝ) • endCommutator (A : End55) (B : End55)
  rw [endCommutator_derivation, hA, hB]
  simp only [endCommutator, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, Int.cast_add, add_smul]
  module

/-- Typed bracket map between homogeneous spaces. -/
def contactGradeBracket (k l : ℤ) :
    contactGradeSpace k →ₗ[ℝ]
      contactGradeSpace l →ₗ[ℝ]
        contactGradeSpace (k + l) where
  toFun A :=
    { toFun := fun B =>
        ⟨⁅(A : O55Lie), (B : O55Lie)⁆,
          contactGrade_bracket A.property B.property⟩
      map_add' := by
        intro B C
        apply Subtype.ext
        simp
      map_smul' := by
        intro c B
        apply Subtype.ext
        simp }
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro C
    apply Subtype.ext
    simp
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro B
    apply Subtype.ext
    simp

/-- A vector is homogeneous for the Euler action. -/
def IsVectorWeight (a : ℤ) (u : Vector55) : Prop :=
  contactEulerEnd u = (a : ℝ) • u

/-- Coordinate vectors are Euler eigenvectors. -/
theorem coordinateVector_weight (i : Fin 10) :
    IsVectorWeight (contactWeight i) (coordinateVector i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [IsVectorWeight, contactEulerEnd_apply, coordinateVector,
      contactWeightR]
  · simp [IsVectorWeight, contactEulerEnd_apply, coordinateVector, hji]

/-- Rank-two split-skew generator
`R(u,v)x = B(v,x)u - B(u,x)v`. -/
def splitRankTwoEnd (u v : Vector55) : End55 where
  toFun x := splitPairing v x • u - splitPairing u x • v
  map_add' x y := by
    simp [splitPairing_add_right, add_smul, sub_eq_add_neg]
    module
  map_smul' c x := by
    simp [splitPairing_smul_right, smul_smul]
    module

@[simp] theorem splitRankTwoEnd_apply (u v x : Vector55) :
    splitRankTwoEnd u v x =
      splitPairing v x • u - splitPairing u x • v := rfl

/-- Rank-two generators are infinitesimal split isometries. -/
theorem splitRankTwo_isSplitSkew (u v : Vector55) :
    IsSplitSkew (splitRankTwoEnd u v) := by
  intro x y
  simp only [splitRankTwoEnd_apply, splitPairing_sub_left,
    splitPairing_sub_right, splitPairing_smul_left,
    splitPairing_smul_right]
  rw [splitPairing_comm u y, splitPairing_comm v y]
  ring

/-- Rank-two generator inside `so(5,5)`. -/
def splitRankTwo (u v : Vector55) : O55Lie :=
  ⟨splitRankTwoEnd u v, splitRankTwo_isSplitSkew u v⟩

/-- A rank-two generator has degree equal to the sum of vector weights. -/
theorem splitRankTwo_grade
    {a b : ℤ} {u v : Vector55}
    (hu : IsVectorWeight a u)
    (hv : IsVectorWeight b v) :
    splitRankTwo u v ∈ contactGradeSpace (a + b) := by
  unfold IsVectorWeight at hu hv
  change endCommutator contactEulerEnd (splitRankTwoEnd u v) =
    ((a + b : ℤ) : ℝ) • splitRankTwoEnd u v
  apply LinearMap.ext
  intro x
  have hBu : splitPairing u (contactEulerEnd x) =
      -(a : ℝ) * splitPairing u x := by
    have h := contactEuler_isSplitSkew u x
    rw [hu, splitPairing_smul_left] at h
    linarith
  have hBv : splitPairing v (contactEulerEnd x) =
      -(b : ℝ) * splitPairing v x := by
    have h := contactEuler_isSplitSkew v x
    rw [hv, splitPairing_smul_left] at h
    linarith
  simp only [endCommutator_apply, splitRankTwoEnd_apply,
    map_sub, map_smul, hu, hv, hBu, hBv,
    Int.cast_add, smul_sub, smul_smul]
  module

/-- Canonical witnesses for the five contact degrees. -/
def gradeMinusTwo : O55Lie :=
  splitRankTwo (coordinateVector 0) (coordinateVector 1)

def gradeMinusOne : O55Lie :=
  splitRankTwo (coordinateVector 0) (coordinateVector 2)

def gradeZero : O55Lie :=
  splitRankTwo (coordinateVector 2) (coordinateVector 3)

def gradePlusOne : O55Lie :=
  splitRankTwo (coordinateVector 8) (coordinateVector 2)

def gradePlusTwo : O55Lie :=
  splitRankTwo (coordinateVector 8) (coordinateVector 9)

/-- Every contact lane is inhabited. -/
theorem five_grades_inhabited :
    gradeMinusTwo ∈ contactGradeSpace (-2) ∧
      gradeMinusOne ∈ contactGradeSpace (-1) ∧
      gradeZero ∈ contactGradeSpace 0 ∧
      gradePlusOne ∈ contactGradeSpace 1 ∧
      gradePlusTwo ∈ contactGradeSpace 2 := by
  exact ⟨by
      simpa [gradeMinusTwo, contactWeight] using
        splitRankTwo_grade (coordinateVector_weight 0)
          (coordinateVector_weight 1),
    by
      simpa [gradeMinusOne, contactWeight] using
        splitRankTwo_grade (coordinateVector_weight 0)
          (coordinateVector_weight 2),
    by
      simpa [gradeZero, contactWeight] using
        splitRankTwo_grade (coordinateVector_weight 2)
          (coordinateVector_weight 3),
    by
      simpa [gradePlusOne, contactWeight, add_comm] using
        splitRankTwo_grade (coordinateVector_weight 8)
          (coordinateVector_weight 2),
    by
      simpa [gradePlusTwo, contactWeight] using
        splitRankTwo_grade (coordinateVector_weight 8)
          (coordinateVector_weight 9)⟩

/-- Crosscap conjugation reverses the Euler element. -/
theorem crosscapConjugation_euler :
    crosscapConjugation contactEuler = -contactEuler := by
  apply Subtype.ext
  exact crosscap_conjugates_euler

/-- Crosscap conjugation reverses every contact degree. -/
theorem crosscap_reverses_grade
    {k : ℤ} {A : O55Lie}
    (hA : A ∈ contactGradeSpace k) :
    crosscapConjugation A ∈ contactGradeSpace (-k) := by
  unfold contactGradeSpace IsContactGrade at hA ⊢
  change endCommutator contactEulerEnd
      (crosscapEnd * (A : End55) * crosscapEnd) =
    ((-k : ℤ) : ℝ) •
      (crosscapEnd * (A : End55) * crosscapEnd)
  calc
    endCommutator contactEulerEnd
        (crosscapEnd * (A : End55) * crosscapEnd) =
      -(crosscapEnd *
          endCommutator contactEulerEnd (A : End55) * crosscapEnd) := by
        unfold endCommutator
        noncomm_ring [crosscapEnd_sq, crosscap_anticommutes_euler]
    _ = -(crosscapEnd * ((k : ℝ) • (A : End55)) * crosscapEnd) := by
        rw [hA]
    _ = ((-k : ℤ) : ℝ) •
        (crosscapEnd * (A : End55) * crosscapEnd) := by
        simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

end InfoGeometry.Orthogonal.O55Contact
