import InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelContinuityReduction
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFrechetBridge

/-!
# Traced two-point consequence of the noncommutative Duhamel identity

This owner applies the already existing continuous linear functional
tracedRightMulCLM to the real Fréchet/Duhamel operator identity.  It proves
the two-insertion trace formula without a spectral decomposition and without
commutativity assumptions on H, A, or B.

The theorem is deliberately stated for the real Fréchet derivative.  Relating
it to the complex-linear derivative used by the holomorphic two-point owner is
a separate restriction-of-scalars theorem and is not hidden by coercions here.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 800000

namespace InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge

open MeasureTheory
open scoped Interval
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/--
Applying trace after right multiplication to the Duhamel operator commutes
with the Bochner interval integral.
-/
theorem trace_duhamelDerivative_mul_eq_duhamelTwoPoint
    {n : ℕ} (H A B : Operator n) :
    finiteOperatorTrace (duhamelDerivative H A * B) =
      ∫ s in (0 : ℝ)..1,
        finiteOperatorTrace
          (NormedSpace.exp ((1 - s) • H) *
            A *
              NormedSpace.exp (s • H) *
                B) := by
  let f : ℝ → Operator n := fun s =>
    NormedSpace.exp ((1 - s) • H) *
      A *
        NormedSpace.exp (s • H)
  have hf : IntervalIntegrable f volume (0 : ℝ) 1 :=
    intervalIntegrable_duhamelOperatorIntegrand H A
  rw [duhamelDerivative_apply_integral]
  change
    ((tracedRightMulCLM B).restrictScalars ℝ) (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (0 : ℝ)..1, ((tracedRightMulCLM B).restrictScalars ℝ) (f s)
  exact (((tracedRightMulCLM B).restrictScalars ℝ).intervalIntegral_comp_comm hf).symm

/--
The two-insertion trace of the changed-origin real Fréchet derivative is the
Duhamel two-point integral.  This is the scalar theorem needed before Gibbs
normalisation and CFC real-power transport.
-/
theorem trace_exponentialDerivative_mul_eq_duhamelTwoPoint
    {n : ℕ} (H A B : Operator n) :
    finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℝ) H A * B) =
      ∫ s in (0 : ℝ)..1,
        finiteOperatorTrace
          (NormedSpace.exp ((1 - s) • H) *
            A *
              NormedSpace.exp (s • H) *
                B) := by
  have hcont :
      ContinuousAt
        (InfoGeometry.OperatorAlgebra.duhamelDifferenceQuotient H A) 0 :=
    (InfoGeometry.OperatorAlgebra.continuous_duhamelDifferenceQuotient H A).continuousAt
  have hderiv :=
    InfoGeometry.OperatorAlgebra.exponentialDerivative_apply_eq_duhamelDerivative_of_continuousAt
      H A hcont
  rw [hderiv]
  exact trace_duhamelDerivative_mul_eq_duhamelTwoPoint H A B

end InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge
