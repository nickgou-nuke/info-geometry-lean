import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# RestorePrimitiveSigmaBridge2

Small sandbox packet for the primitive/divisor analytic bridge.
-/

namespace InfoGeometry.Restore.PrimitiveSigmaBridge2

open scoped BigOperators

/-- Prime interval packet: primitive and supported above the lower bound. -/
theorem primeFinsetIcc_packet (x N : ℕ) :
    InfoGeometry.Arithmetic.PrimitiveFinset (InfoGeometry.Arithmetic.primeFinsetIcc x N) ∧
      InfoGeometry.Arithmetic.SupportedAboveFinset x (InfoGeometry.Arithmetic.primeFinsetIcc x N) := by
  constructor
  · exact InfoGeometry.Arithmetic.primeFinsetIcc_primitive x N
  · exact InfoGeometry.Arithmetic.primeFinsetIcc_supportedAbove x N

/-- Logarithmic divisor-sum bridge. -/
theorem primitiveWeight_vonMangoldt_divisorSum_eq_log_restore
    (A : Finset ℕ) :
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Finset.sum a.divisors InfoGeometry.Arithmetic.realVonMangoldt)
      =
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Real.log a) := by
  exact InfoGeometry.Arithmetic.primitiveWeight_vonMangoldt_divisorSum_eq_log A

/-- Primitive weight controlled by the divisor sigma bridge. -/
theorem primitiveWeightSum_le_div_log_mul_sigma_restore
    {A : Finset ℕ} {x : ℕ} (hx : 2 ≤ x)
    (hAsupp : InfoGeometry.Arithmetic.SupportedAboveFinset x A) :
    InfoGeometry.Arithmetic.primitiveWeightSum A
      ≤ (1 / Real.log x)
          * Finset.sum (A.sigma fun a => a.divisors)
              (fun y => InfoGeometry.Arithmetic.primitiveWeight y.1 * InfoGeometry.Arithmetic.realVonMangoldt y.2) := by
  exact InfoGeometry.Arithmetic.primitiveWeightSum_le_div_log_mul_sigma hx hAsupp

end InfoGeometry.Restore.PrimitiveSigmaBridge2
