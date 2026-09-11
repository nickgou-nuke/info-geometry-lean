import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.CuntzLeftRightCommutant

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzGNSRepresentation

noncomputable section

variable {n : ℕ}

abbrev CuntzOperator (n : ℕ) := CuntzAlg n →ₗ[ℂ] CuntzAlg n

/-- Left multiplication on the native Cuntz quotient. -/
noncomputable def leftMultiplication
    (n : ℕ) (a : CuntzAlg n) : CuntzOperator n :=
  LinearMap.mulLeft ℂ a

@[simp] theorem leftMultiplication_apply
    (n : ℕ) (a x : CuntzAlg n) :
    leftMultiplication n a x = a * x := by
  rfl

/-- Right multiplication on the native Cuntz quotient. -/
noncomputable def rightMultiplication
    (n : ℕ) (a : CuntzAlg n) : CuntzOperator n :=
  LinearMap.mulRight ℂ a

@[simp] theorem rightMultiplication_apply
    (n : ℕ) (a x : CuntzAlg n) :
    rightMultiplication n a x = x * a := by
  rfl

theorem left_right_commute
    (n : ℕ) (a b x : CuntzAlg n) :
    leftMultiplication n a (rightMultiplication n b x) =
      rightMultiplication n b (leftMultiplication n a x) := by
  simp [leftMultiplication, rightMultiplication, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

/-- The commutant of the left regular Cuntz action. -/
def leftRegularCommutant (n : ℕ) : Set (CuntzOperator n) :=
  {T | ∀ a x : CuntzAlg n,
    T (leftMultiplication n a x) = leftMultiplication n a (T x)}

theorem rightMultiplication_mem_leftRegularCommutant
    (n : ℕ) (b : CuntzAlg n) :
    rightMultiplication n b ∈ leftRegularCommutant n := by
  intro a x
  exact (left_right_commute n a b x).symm

/-- Every operator commuting with all left multiplications is right
multiplication by its value at the unit. -/
theorem leftRegularCommutant_eq_rightMultiplicationRange
    (n : ℕ) :
    leftRegularCommutant n =
      {T | ∃ b : CuntzAlg n, T = rightMultiplication n b} := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    ext x
    have h := hT x 1
    simpa [leftMultiplication, rightMultiplication,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using h
  · rintro ⟨b, rfl⟩
    exact rightMultiplication_mem_leftRegularCommutant n b

/-- The native algebraic Tomita mirror exchanges left multiplication with
right multiplication by the starred element. -/
theorem star_conjugates_left_to_right
    (n : ℕ) (a x : CuntzAlg n) :
    star (a * star x) = rightMultiplication n (star a) x := by
  simp [rightMultiplication, LinearMap.mulRight_apply]

end

end InfoGeometry.Algebra.CuntzLeftRightCommutant
