import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# RestorePrimitiveAnalyticPacket2

Small sandbox packet for primitive-set analytic readbacks.
-/

namespace InfoGeometry.Restore.PrimitiveAnalyticPacket2

open scoped BigOperators

/-- Primitive weight is nonnegative. -/
theorem primitiveWeight_nonneg_restore (n : ℕ) :
    0 ≤ InfoGeometry.Arithmetic.primitiveWeight n := by
  exact InfoGeometry.Arithmetic.primitiveWeight_nonneg n

/-- The total primitive-weight sum is nonnegative. -/
theorem primitiveWeightSum_nonneg_restore (A : Finset ℕ) :
    0 ≤ InfoGeometry.Arithmetic.primitiveWeightSum A := by
  exact InfoGeometry.Arithmetic.primitiveWeightSum_nonneg A

/-- Primitive weight summed against von Mangoldt divisors equals the log readout. -/
theorem primitiveWeight_vonMangoldt_divisorSum_eq_log_restore (A : Finset ℕ) :
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Finset.sum a.divisors InfoGeometry.Arithmetic.realVonMangoldt)
      =
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Real.log a) := by
  exact InfoGeometry.Arithmetic.primitiveWeight_vonMangoldt_divisorSum_eq_log A

/-- Primitive weight is controlled by the divisor-sigma bridge. -/
theorem primitiveWeightSum_le_div_log_mul_sigma_restore
    {A : Finset ℕ} {x : ℕ} (hx : 2 ≤ x)
    (hAsupp : InfoGeometry.Arithmetic.SupportedAboveFinset x A) :
    InfoGeometry.Arithmetic.primitiveWeightSum A
      ≤ (1 / Real.log x)
          * Finset.sum (A.sigma fun a => a.divisors)
              (fun y => InfoGeometry.Arithmetic.primitiveWeight y.1 * InfoGeometry.Arithmetic.realVonMangoldt y.2) := by
  exact InfoGeometry.Arithmetic.primitiveWeightSum_le_div_log_mul_sigma hx hAsupp

end InfoGeometry.Restore.PrimitiveAnalyticPacket2
