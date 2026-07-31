import Mathlib.Tactic
import Omega.Discussion.HypercubeStokesFourierBinomial

namespace Omega.Discussion

/-- The Stokes/Fourier dictionary, weighted spectral rewrite, tailwise binomial lower bound, and
rearrangement imply the stated spectral-tail estimate. -/
theorem paper_discussion_spectral_tail_bound_from_flux
    (hypercubeStokesFourierBinomialPackage weightedSpectralLayerRewrite
      chooseTailLowerBound tailRearrangement spectralTailBound : Prop)
    (hypercubeStokesFourierBinomialPackage_h : hypercubeStokesFourierBinomialPackage)
    (weightedSpectralLayerRewrite_h : weightedSpectralLayerRewrite)
    (chooseTailLowerBound_h : chooseTailLowerBound)
    (tailRearrangement_h : tailRearrangement)
    (deriveSpectralTailBound :
      hypercubeStokesFourierBinomialPackage → weightedSpectralLayerRewrite →
        chooseTailLowerBound → tailRearrangement → spectralTailBound) :
    spectralTailBound := by
  exact deriveSpectralTailBound hypercubeStokesFourierBinomialPackage_h
    weightedSpectralLayerRewrite_h chooseTailLowerBound_h tailRearrangement_h

end Omega.Discussion
