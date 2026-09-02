import InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFrechetBridge
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Traced two-point consequence of the noncommutative Duhamel identity

This owner applies the existing continuous linear functional
tracedRightMulCLM to the real Fréchet--Duhamel operator identity.  It proves
the two-insertion trace formula without spectral decomposition and without
commutativity assumptions on H, A, or B.

The theorem is deliberately stated for the real Fréchet derivative.  Relating
it to the complex-linear derivative used by the holomorphic two-point owner is
a separate restriction-of-scalars theorem and is not hidden by coercions here.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge

open MeasureTheory
open scoped Interval
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
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
  have hf : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    fun_prop
  rw [duhamelDerivative_apply_integral]
  change
    tracedRightMulCLM B (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (0 : ℝ)..1, tracedRightMulCLM B (f s)
  exact ((tracedRightMulCLM B).intervalIntegral_comp_comm hf).symm

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
  rw [exponentialDerivative_apply_eq_duhamelDerivative]
  exact trace_duhamelDerivative_mul_eq_duhamelTwoPoint H A B

/--
The complex changed-origin exponential derivative restricts to the real
changed-origin derivative.  This is derivative uniqueness for the same
Banach-algebra exponential, not an additional analytic hypothesis.
-/
theorem exponentialDerivative_complex_restrictScalars_eq_real
    {n : ℕ} (H : Operator n) :
    (exponentialDerivative (𝕜 := ℂ) H).restrictScalars ℝ =
      exponentialDerivative (𝕜 := ℝ) H := by
  have hComplexReal :
      HasFDerivAt NormedSpace.exp
        ((exponentialDerivative (𝕜 := ℂ) H).restrictScalars ℝ) H :=
    (hasFDerivAt_exp_noncommutative
      (𝕜 := ℂ) (A := Operator n) H).restrictScalars ℝ
  have hReal :
      HasFDerivAt NormedSpace.exp
        (exponentialDerivative (𝕜 := ℝ) H) H :=
    hasFDerivAt_exp_noncommutative
      (𝕜 := ℝ) (A := Operator n) H
  exact hComplexReal.unique hReal

/-- Pointwise complex/real compatibility in every operator direction. -/
theorem exponentialDerivative_complex_apply_eq_real
    {n : ℕ} (H A : Operator n) :
    exponentialDerivative (𝕜 := ℂ) H A =
      exponentialDerivative (𝕜 := ℝ) H A := by
  have h := congrArg
    (fun L : Operator n →L[ℝ] Operator n => L A)
    (exponentialDerivative_complex_restrictScalars_eq_real H)
  exact h

/--
Complex Fréchet version of the two-insertion Wilcox--Duhamel trace identity.
This now matches the derivative used by the existing holomorphic two-point
numerator owner.
-/
theorem trace_complexExponentialDerivative_mul_eq_duhamelTwoPoint
    {n : ℕ} (H A B : Operator n) :
    finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H A * B) =
      ∫ s in (0 : ℝ)..1,
        finiteOperatorTrace
          (NormedSpace.exp ((1 - s) • H) *
            A *
              NormedSpace.exp (s • H) *
                B) := by
  rw [exponentialDerivative_complex_apply_eq_real]
  exact trace_exponentialDerivative_mul_eq_duhamelTwoPoint H A B

end InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge
