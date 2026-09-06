import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- Numerical carrier for the zeta-spectral HSZK bridge. -/
structure ZetaSpectralHSZKData where
  partitionAmplitude : ℝ
  smoothedSffUpperBound : ℝ
  framePotentialGap : ℝ
  hszkError : ℝ

/-- The squared partition amplitude propagates through the smoothed SFF and frame-potential
windows to the final HSZK error bound. -/
theorem paper_discussion_zeta_spectral_hszk
    (D : ZetaSpectralHSZKData)
    (partitionControlsSff :
      D.partitionAmplitude ^ 2 ≤ D.smoothedSffUpperBound)
    (sffControlsFramePotential :
      D.smoothedSffUpperBound ≤ D.framePotentialGap)
    (framePotentialControlsHSZK :
      D.framePotentialGap ≤ D.hszkError) :
    D.partitionAmplitude ^ 2 ≤ D.hszkError := by
  exact le_trans (le_trans partitionControlsSff sffControlsFramePotential)
    framePotentialControlsHSZK

end Omega.Discussion
