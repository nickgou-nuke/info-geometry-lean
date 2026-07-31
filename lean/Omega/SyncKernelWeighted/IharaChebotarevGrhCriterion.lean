import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete square-root error predicate for the Ihara--Chebotarev error exponent. -/
def iharaChebotarevSquareRootError (lambdaOne Lambda : ℝ) : Prop :=
  Lambda ^ (2 : ℕ) ≤ lambdaOne

/-- Concrete Ramanujan/GRH-type spectral-gap predicate. -/
def iharaChebotarevSpectralGap (lambdaOne Lambda : ℝ) : Prop :=
  Lambda ≤ Real.sqrt lambdaOne

/-- The Ihara--Chebotarev square-root error criterion is equivalent to the Ramanujan/GRH-type
spectral-gap condition once the forward and backward implications from the expansion theorem are
recorded.
    cor:ihara-chebotarev-grh-criterion -/
theorem paper_ihara_chebotarev_grh_criterion
    (lambdaOne Lambda : ℝ)
    (squareRootError_implies_spectralGap :
      iharaChebotarevSquareRootError lambdaOne Lambda →
        iharaChebotarevSpectralGap lambdaOne Lambda)
    (spectralGap_implies_squareRootError :
      iharaChebotarevSpectralGap lambdaOne Lambda →
        iharaChebotarevSquareRootError lambdaOne Lambda) :
    iharaChebotarevSquareRootError lambdaOne Lambda ↔
      iharaChebotarevSpectralGap lambdaOne Lambda := by
  refine Iff.intro ?_ ?_
  · exact squareRootError_implies_spectralGap
  · exact spectralGap_implies_squareRootError

end Omega.SyncKernelWeighted
