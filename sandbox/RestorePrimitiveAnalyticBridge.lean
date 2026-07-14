import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# RestorePrimitiveAnalyticBridge

Small sandbox packet for primitive-set analytic divisor identities.
-/

namespace InfoGeometry.Restore.PrimitiveAnalyticBridge

open scoped BigOperators

/-- Prime interval packet: primitive and supported above the lower bound. -/
theorem primeFinsetIcc_packet (x N : ℕ) :
    InfoGeometry.Arithmetic.PrimitiveFinset (InfoGeometry.Arithmetic.primeFinsetIcc x N) ∧
      InfoGeometry.Arithmetic.SupportedAboveFinset x (InfoGeometry.Arithmetic.primeFinsetIcc x N) := by
  constructor
  · exact InfoGeometry.Arithmetic.primeFinsetIcc_primitive x N
  · exact InfoGeometry.Arithmetic.primeFinsetIcc_supportedAbove x N

/-- The primitive weight sums the Mellin kernel over the finite support. -/
theorem primitiveWeightSum_eq_integral_mellinKernel (A : Finset ℕ) :
    InfoGeometry.Arithmetic.primitiveWeightSum A =
      ∫ s : ℝ in Set.Ioi 1, Finset.sum A (fun n => InfoGeometry.Arithmetic.primitiveMellinKernel n s) := by
  exact InfoGeometry.Arithmetic.primitiveWeightSum_eq_integral_mellinKernel A

/-- The divisor-sigma readout of the primitive weight. -/
theorem primitiveWeight_vonMangoldt_divisorSigma_eq (A : Finset ℕ) :
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Finset.sum a.divisors InfoGeometry.Arithmetic.realVonMangoldt)
      =
    Finset.sum (A.sigma fun a => a.divisors) (fun x => InfoGeometry.Arithmetic.primitiveWeight x.1 * InfoGeometry.Arithmetic.realVonMangoldt x.2) := by
  exact InfoGeometry.Arithmetic.primitiveWeight_vonMangoldt_divisorSigma_eq A

/-- The logarithmic divisor-sum readout. -/
theorem primitiveWeight_vonMangoldt_divisorSum_eq_log (A : Finset ℕ) :
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Finset.sum a.divisors InfoGeometry.Arithmetic.realVonMangoldt)
      =
    Finset.sum A (fun a => InfoGeometry.Arithmetic.primitiveWeight a * Real.log a) := by
  exact InfoGeometry.Arithmetic.primitiveWeight_vonMangoldt_divisorSum_eq_log A

/-- Upper bound by the von Mangoldt sigma-sum divided by `log x`. -/
theorem primitiveWeightSum_le_div_log_mul_sigma
    {A : Finset ℕ} {x : ℕ} (hx : 2 ≤ x)
    (hAsupp : InfoGeometry.Arithmetic.SupportedAboveFinset x A) :
    InfoGeometry.Arithmetic.primitiveWeightSum A
      ≤ (1 / Real.log x)
          * Finset.sum (A.sigma fun a => a.divisors)
              (fun y => InfoGeometry.Arithmetic.primitiveWeight y.1 * InfoGeometry.Arithmetic.realVonMangoldt y.2) := by
  exact InfoGeometry.Arithmetic.primitiveWeightSum_le_div_log_mul_sigma hx hAsupp

end InfoGeometry.Restore.PrimitiveAnalyticBridge
