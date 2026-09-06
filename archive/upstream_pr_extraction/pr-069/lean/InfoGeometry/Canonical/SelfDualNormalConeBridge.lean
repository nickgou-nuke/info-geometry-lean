import InfoGeometry.Arithmetic.ProjectiveEntropy

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectiveRelativeEntropy

open InfoGeometry.Thermodynamics.ProjectiveTemperature
open InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature
open InfoGeometry.Arithmetic.ProjectiveEntropy

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

#### BUCKET 3: OPEN CLOSURE DEBT
[Exact theorem statements that remain unproved. No wrappers, interfaces, fields, witnesses, certificates, or renamed placeholders.]
-/

/-- Unnormalized KL-style scalar readout. -/
def projectiveKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q)

/-- KL-style readout comparing a primitive projective density against a finite von-Mangoldt density. -/
def primitiveToPrimeProjectiveKL
    (candidate reference : Finset ℕ) (u : ℝ) : ℝ :=
  projectiveKL
    (primitiveInvertedPartitionDensity candidate u)
    (arithmeticPrimeInvertedPartitionDensity reference u)

/-- The opposite orientation: finite von-Mangoldt density against the primitive density. -/
def primeToPrimitiveProjectiveKL
    (candidate reference : Finset ℕ) (u : ℝ) : ℝ :=
  projectiveKL
    (arithmeticPrimeInvertedPartitionDensity reference u)
    (primitiveInvertedPartitionDensity candidate u)

/-- Unfolding of the primitive-to-prime KL-style readout. -/
theorem primitiveToPrimeProjectiveKL_eq
    (candidate reference : Finset ℕ) (u : ℝ) :
    primitiveToPrimeProjectiveKL candidate reference u =
      primitiveInvertedPartitionDensity candidate u *
        Real.log
          (primitiveInvertedPartitionDensity candidate u /
            arithmeticPrimeInvertedPartitionDensity reference u) :=
  rfl

/-- Unfolding of the prime-to-primitive KL-style readout. -/
theorem primeToPrimitiveProjectiveKL_eq
    (candidate reference : Finset ℕ) (u : ℝ) :
    primeToPrimitiveProjectiveKL candidate reference u =
      arithmeticPrimeInvertedPartitionDensity reference u *
        Real.log
          (arithmeticPrimeInvertedPartitionDensity reference u /
            primitiveInvertedPartitionDensity candidate u) :=
  rfl

/-- Scalar KL readout is nonnegative when the mass is nonnegative and the ratio is at least one. -/
theorem projectiveKL_nonneg_of_nonneg_of_one_le_ratio
    {p q : ℝ} (hp : 0 ≤ p) (hratio : 1 ≤ p / q) :
    0 ≤ projectiveKL p q := by
  unfold projectiveKL
  exact mul_nonneg hp (Real.log_nonneg hratio)

/-- Scalar KL readout is positive when the mass is positive and the ratio is greater than one. -/
theorem projectiveKL_pos_of_pos_of_one_lt_ratio
    {p q : ℝ} (hp : 0 < p) (hratio : 1 < p / q) :
    0 < projectiveKL p q := by
  unfold projectiveKL
  exact mul_pos hp (Real.log_pos hratio)

/-- Scalar KL readout vanishes on equal nonzero arguments. -/
theorem projectiveKL_eq_zero_of_eq_of_ne_zero
    {p q : ℝ} (h : p = q) (hp : p ≠ 0) :
    projectiveKL p q = 0 := by
  subst q
  unfold projectiveKL
  rw [div_self hp, Real.log_one, mul_zero]

/-- Primitive-to-prime readout is nonnegative under the corresponding scalar ratio property. -/
theorem primitiveToPrimeProjectiveKL_nonneg_of_one_le_ratio
    (candidate reference : Finset ℕ) (u : ℝ)
    (hp : 0 ≤ primitiveInvertedPartitionDensity candidate u)
    (hratio :
      1 ≤
        primitiveInvertedPartitionDensity candidate u /
          arithmeticPrimeInvertedPartitionDensity reference u) :
    0 ≤ primitiveToPrimeProjectiveKL candidate reference u := by
  exact projectiveKL_nonneg_of_nonneg_of_one_le_ratio hp hratio

/-- Primitive-to-prime readout is positive under the corresponding scalar ratio property. -/
theorem primitiveToPrimeProjectiveKL_pos_of_one_lt_ratio
    (candidate reference : Finset ℕ) (u : ℝ)
    (hp : 0 < primitiveInvertedPartitionDensity candidate u)
    (hratio :
      1 <
        primitiveInvertedPartitionDensity candidate u /
          arithmeticPrimeInvertedPartitionDensity reference u) :
    0 < primitiveToPrimeProjectiveKL candidate reference u := by
  exact projectiveKL_pos_of_pos_of_one_lt_ratio hp hratio

/-- Primitive-to-prime readout vanishes when the two finite densities agree and are nonzero. -/
theorem primitiveToPrimeProjectiveKL_eq_zero_of_density_eq
    (candidate reference : Finset ℕ) (u : ℝ)
    (h :
      primitiveInvertedPartitionDensity candidate u =
        arithmeticPrimeInvertedPartitionDensity reference u)
    (hp : primitiveInvertedPartitionDensity candidate u ≠ 0) :
    primitiveToPrimeProjectiveKL candidate reference u = 0 := by
  exact projectiveKL_eq_zero_of_eq_of_ne_zero h hp

/-- Prime-to-primitive readout is nonnegative under the corresponding scalar ratio property. -/
theorem primeToPrimitiveProjectiveKL_nonneg_of_one_le_ratio
    (candidate reference : Finset ℕ) (u : ℝ)
    (hp : 0 ≤ arithmeticPrimeInvertedPartitionDensity reference u)
    (hratio :
      1 ≤
        arithmeticPrimeInvertedPartitionDensity reference u /
          primitiveInvertedPartitionDensity candidate u) :
    0 ≤ primeToPrimitiveProjectiveKL candidate reference u := by
  exact projectiveKL_nonneg_of_nonneg_of_one_le_ratio hp hratio

/-- Prime-to-primitive readout is positive under the corresponding scalar ratio property. -/
theorem primeToPrimitiveProjectiveKL_pos_of_one_lt_ratio
    (candidate reference : Finset ℕ) (u : ℝ)
    (hp : 0 < arithmeticPrimeInvertedPartitionDensity reference u)
    (hratio :
      1 <
        arithmeticPrimeInvertedPartitionDensity reference u /
          primitiveInvertedPartitionDensity candidate u) :
    0 < primeToPrimitiveProjectiveKL candidate reference u := by
  exact projectiveKL_pos_of_pos_of_one_lt_ratio hp hratio

/-- Prime-to-primitive readout vanishes when the two finite densities agree and are nonzero. -/
theorem primeToPrimitiveProjectiveKL_eq_zero_of_density_eq
    (candidate reference : Finset ℕ) (u : ℝ)
    (h :
      arithmeticPrimeInvertedPartitionDensity reference u =
        primitiveInvertedPartitionDensity candidate u)
    (hp : arithmeticPrimeInvertedPartitionDensity reference u ≠ 0) :
    primeToPrimitiveProjectiveKL candidate reference u = 0 := by
  exact projectiveKL_eq_zero_of_eq_of_ne_zero h hp

end InfoGeometry.Arithmetic.ProjectiveRelativeEntropy
