import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# RestorePrimitiveWeights

Small sandbox packet for primitive-weight and von Mangoldt readbacks.
-/

namespace InfoGeometry.Restore.PrimitiveWeights

open scoped BigOperators

/-- Primitive weight is nonnegative. -/
theorem primitiveWeight_nonneg (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.primitiveWeight n := by
  exact InfoGeometry.Arithmetic.primitiveWeight_nonneg n

/-- Real von Mangoldt is nonnegative. -/
theorem realVonMangoldt_nonneg (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.realVonMangoldt n := by
  exact InfoGeometry.Arithmetic.realVonMangoldt_nonneg n

/-- Primitive-weight sums are monotone under inclusion. -/
theorem primitiveWeightSum_mono
    {A B : Finset ℕ}
    (hAB : A ⊆ B) :
    InfoGeometry.Arithmetic.primitiveWeightSum A ≤
      InfoGeometry.Arithmetic.primitiveWeightSum B := by
  exact InfoGeometry.Arithmetic.primitiveWeightSum_mono hAB

/-- Primitive indicator series is pointwise nonnegative. -/
theorem primitiveIndicatorSeries_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.primitiveIndicatorSeries A n := by
  exact InfoGeometry.Arithmetic.primitiveIndicatorSeries_nonneg A n

end InfoGeometry.Restore.PrimitiveWeights
