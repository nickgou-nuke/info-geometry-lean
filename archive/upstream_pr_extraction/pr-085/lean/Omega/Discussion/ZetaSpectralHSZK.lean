import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- The squared partition amplitude propagates through the smoothed SFF and frame-potential
    windows to the final HSZK error bound. -/
theorem paper_discussion_zeta_spectral_hszk
    (partitionAmplitude smoothedSffUpperBound framePotentialGap hszkError : ℝ)
    (partitionControlsSff : partitionAmplitude ^ 2 ≤ smoothedSffUpperBound)
    (sffControlsFramePotential : smoothedSffUpperBound ≤ framePotentialGap)
    (framePotentialControlsHSZK : framePotentialGap ≤ hszkError) :
    partitionAmplitude ^ 2 ≤ hszkError := by
  exact le_trans (le_trans partitionControlsSff sffControlsFramePotential)
    framePotentialControlsHSZK

end Omega.Discussion
