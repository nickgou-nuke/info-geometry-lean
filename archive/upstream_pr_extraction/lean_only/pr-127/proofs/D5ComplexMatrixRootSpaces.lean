import proofs.A2InsideD5RootSubsystem

/-! # Complex `D₅` root matrices in an isotropic basis -/

noncomputable section
namespace D5ComplexMatrixRootSpaces

abbrev Half := Fin 5
abbrev IsoIndex := Half ⊕ Half
abbrev CM10 := Matrix IsoIndex IsoIndex ℂ

/-- Split symmetric form pairing the two isotropic halves. -/
def splitMetric : CM10
  | .inl i, .inr j => if i = j then 1 else 0
  | .inr i, .inl j => if i = j then 1 else 0
  | _, _ => 0

/-- Standard diagonal Cartan element `diag(h,-h)`. -/
def cartan (h : Half → ℂ) : CM10
  | .inl i, .inl j => if i = j then h i else 0
  | .inr i, .inr j => if i = j then -h i else 0
  | _, _ => 0

/-- Root vector for the root `eᵢ-eⱼ`. -/
def differenceRootMatrix (i j : Half) : CM10
  | .inl a, .inl b => if a = i ∧ b = j then 1 else 0
  | .inr a, .inr b => if a = j ∧ b = i then -1 else 0
  | _, _ => 0

/-- Root vector for `eᵢ+eⱼ`. -/
def sumRootMatrix (i j : Half) : CM10
  | .inl a, .inr b => if a = i ∧ b = j then 1 else
      if a = j ∧ b = i then -1 else 0
  | _, _ => 0

/-- Root vector for `-eᵢ-eⱼ`. -/
def negSumRootMatrix (i j : Half) : CM10
  | .inr a, .inl b => if a = i ∧ b = j then 1 else
      if a = j ∧ b = i then -1 else 0
  | _, _ => 0

def IsSplitOrthogonal (A : CM10) : Prop :=
  A.transpose * splitMetric + splitMetric * A = 0

private theorem sum_isoIndex {R : Type*} [AddCommMonoid R] (f : IsoIndex → R) :
    ∑ x, f x = (∑ i : Half, f (.inl i)) + ∑ i : Half, f (.inr i) := by
  exact Fintype.sum_sum_type f

theorem cartan_isSplitOrthogonal (h : Half → ℂ) :
    IsSplitOrthogonal (cartan h) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [IsSplitOrthogonal, Matrix.mul_apply, sum_isoIndex, splitMetric, cartan]
  all_goals by_cases hab : a = b <;> simp_all [eq_comm]

theorem differenceRoot_isSplitOrthogonal (i j : Half) (hij : i ≠ j) :
    IsSplitOrthogonal (differenceRootMatrix i j) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [IsSplitOrthogonal, Matrix.mul_apply, sum_isoIndex,
      splitMetric, differenceRootMatrix]
  all_goals
    by_cases hab : a = b <;> by_cases hai : a = i <;>
      by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;> simp_all [eq_comm]

theorem sumRoot_isSplitOrthogonal (i j : Half) (hij : i ≠ j) :
    IsSplitOrthogonal (sumRootMatrix i j) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [IsSplitOrthogonal, Matrix.mul_apply, sum_isoIndex,
      splitMetric, sumRootMatrix]
  all_goals
    by_cases hab : a = b <;> by_cases hai : a = i <;>
      by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;> simp_all [eq_comm]

theorem negSumRoot_isSplitOrthogonal (i j : Half) (hij : i ≠ j) :
    IsSplitOrthogonal (negSumRootMatrix i j) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [IsSplitOrthogonal, Matrix.mul_apply, sum_isoIndex,
      splitMetric, negSumRootMatrix]
  all_goals
    by_cases hab : a = b <;> by_cases hai : a = i <;>
      by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;> simp_all [eq_comm]

def commutator (A B : CM10) : CM10 := A * B - B * A

theorem cartan_bracket_difference (h : Half → ℂ) (i j : Half) :
    commutator (cartan h) (differenceRootMatrix i j) =
      (h i - h j) • differenceRootMatrix i j := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [commutator, Matrix.mul_apply, sum_isoIndex, cartan,
      differenceRootMatrix]
  all_goals
    by_cases hab : a = b <;> by_cases hai : a = i <;>
      by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;> simp_all [eq_comm] <;> ring

theorem cartan_bracket_sum (h : Half → ℂ) (i j : Half) :
    commutator (cartan h) (sumRootMatrix i j) =
      (h i + h j) • sumRootMatrix i j := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [commutator, Matrix.mul_apply, sum_isoIndex, cartan, sumRootMatrix]
  all_goals
    by_cases hab : a = b <;> by_cases hai : a = i <;>
      by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;> simp_all [eq_comm] <;> ring

theorem cartan_bracket_negSum (h : Half → ℂ) (i j : Half) :
    commutator (cartan h) (negSumRootMatrix i j) =
      (-h i - h j) • negSumRootMatrix i j := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [commutator, Matrix.mul_apply, sum_isoIndex, cartan, negSumRootMatrix]
  all_goals
    by_cases hab : a = b <;> by_cases hai : a = i <;>
      by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;> simp_all [eq_comm] <;> ring

theorem differenceRootMatrix_ne_zero {i j : Half} (hij : i ≠ j) :
    differenceRootMatrix i j ≠ 0 := by
  intro h
  have := congrArg (fun A : CM10 => A (.inl i) (.inl j)) h
  simp [differenceRootMatrix, hij] at this

theorem sumRootMatrix_ne_zero {i j : Half} (hij : i ≠ j) :
    sumRootMatrix i j ≠ 0 := by
  intro h
  have := congrArg (fun A : CM10 => A (.inl i) (.inr j)) h
  simp [sumRootMatrix, hij] at this

theorem negSumRootMatrix_ne_zero {i j : Half} (hij : i ≠ j) :
    negSumRootMatrix i j ≠ 0 := by
  intro h
  have := congrArg (fun A : CM10 => A (.inr i) (.inl j)) h
  simp [negSumRootMatrix, hij] at this

end D5ComplexMatrixRootSpaces
end noncomputable section
