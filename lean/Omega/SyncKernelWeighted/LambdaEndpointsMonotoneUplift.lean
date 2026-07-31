import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The single-flow weighted spectral-radius model. -/
def lambdaFlowSpectralRadius (carryFreeRadius slope u : ℝ) : ℝ :=
  carryFreeRadius + u * slope

/-- The tensor-power uplift across `D.copies` independent flows. -/
def lambdaGlobalSpectralRadius (carryFreeRadius slope : ℝ) (copies : ℕ) (u : ℝ) : ℝ :=
  (lambdaFlowSpectralRadius carryFreeRadius slope u) ^ copies

/-- Concrete statement packaging the endpoint identities, monotonicity, and tensor-power uplift. -/
def LambdaEndpointsMonotoneUpliftStatement
    (carryFreeRadius alphabetSize slope : ℝ) (copies : ℕ) : Prop :=
  lambdaFlowSpectralRadius carryFreeRadius slope 0 = carryFreeRadius ∧
    lambdaFlowSpectralRadius carryFreeRadius slope 1 = alphabetSize ∧
    Monotone (lambdaFlowSpectralRadius carryFreeRadius slope) ∧
    ∀ u : ℝ,
      lambdaGlobalSpectralRadius carryFreeRadius slope copies u =
        (lambdaFlowSpectralRadius carryFreeRadius slope u) ^ copies

/-- Paper label: `prop:lambda-endpoints-monotone-uplift`.
The affine one-flow spectral-radius model has the expected endpoint values, is monotone when the
slope is nonnegative, and tensor-power assembly raises the flow radius to the `copies`th power. -/
theorem paper_lambda_endpoints_monotone_uplift
    (carryFreeRadius alphabetSize slope : ℝ) (copies : ℕ)
    (slope_nonneg : 0 ≤ slope)
    (endpoint_one : carryFreeRadius + slope = alphabetSize) :
    LambdaEndpointsMonotoneUpliftStatement carryFreeRadius alphabetSize slope copies := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [lambdaFlowSpectralRadius]
  · simpa [lambdaFlowSpectralRadius] using endpoint_one
  · intro u v huv
    unfold lambdaFlowSpectralRadius
    have hmul : u * slope ≤ v * slope := mul_le_mul_of_nonneg_right huv slope_nonneg
    linarith
  · intro u
    rfl

end

end Omega.SyncKernelWeighted
