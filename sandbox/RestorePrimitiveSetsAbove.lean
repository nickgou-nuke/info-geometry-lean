import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# RestorePrimitiveSetsAbove

Small sandbox packet for primitive-set and Mangoldt readbacks.
-/

namespace InfoGeometry.Restore.PrimitiveSetsAbove

open scoped BigOperators

/-- Prime interval packet: primitive and supported above the lower bound. -/
theorem primeFinsetIcc_packet (x N : ℕ) :
    InfoGeometry.Arithmetic.PrimitiveFinset (InfoGeometry.Arithmetic.primeFinsetIcc x N) ∧
      InfoGeometry.Arithmetic.SupportedAboveFinset x (InfoGeometry.Arithmetic.primeFinsetIcc x N) := by
  constructor
  · exact InfoGeometry.Arithmetic.primeFinsetIcc_primitive x N
  · exact InfoGeometry.Arithmetic.primeFinsetIcc_supportedAbove x N

/-- Nonnegativity of the primitive weight. -/
theorem primitiveWeight_nonneg (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.primitiveWeight n := by
  exact InfoGeometry.Arithmetic.primitiveWeight_nonneg n

/-- Nonnegativity of the real-valued von Mangoldt weight. -/
theorem realVonMangoldt_nonneg (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.realVonMangoldt n := by
  exact InfoGeometry.Arithmetic.realVonMangoldt_nonneg n

/-- Pointwise nonnegativity of the primitive indicator series. -/
theorem primitiveIndicatorSeries_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.primitiveIndicatorSeries A n := by
  exact InfoGeometry.Arithmetic.primitiveIndicatorSeries_nonneg A n

end InfoGeometry.Restore.PrimitiveSetsAbove
