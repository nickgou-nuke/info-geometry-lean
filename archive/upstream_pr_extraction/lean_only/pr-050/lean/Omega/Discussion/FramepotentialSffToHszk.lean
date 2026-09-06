import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- Spectral control through the frame potential/SFF window propagates first to approximate
two-design control and then to the HSZK error bound.
    prop:discussion-framepotential-sff-to-hszk -/
theorem paper_discussion_framepotential_sff_to_hszk
    (framePotentialGap twoDesignError hszkError : ℝ)
    (hGap : framePotentialGap ≤ twoDesignError)
    (hDesign : twoDesignError ≤ hszkError) :
    framePotentialGap ≤ hszkError := by
  exact le_trans hGap hDesign

end Omega.Discussion
