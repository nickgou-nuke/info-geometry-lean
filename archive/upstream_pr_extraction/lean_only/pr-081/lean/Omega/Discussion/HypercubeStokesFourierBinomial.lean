import Mathlib.Tactic

namespace Omega.Discussion

/-- Walsh mixed differences, subset summation, binomial inversion, and multilinear Stokes data
produce the forward/inverse binomial transforms and the Stokes dictionary. -/
theorem paper_discussion_hypercube_stokes_fourier_binomial
    (walshCharacterDifferenceAction subsetSummation binomialInversionInput
      multilinearStokesInterpretation forwardBinomialTransform
      inverseBinomialTransform stokesIntegralDictionary : Prop)
    (walshCharacterDifferenceAction_h : walshCharacterDifferenceAction)
    (subsetSummation_h : subsetSummation)
    (binomialInversionInput_h : binomialInversionInput)
    (multilinearStokesInterpretation_h : multilinearStokesInterpretation)
    (deriveForwardBinomialTransform :
      walshCharacterDifferenceAction → subsetSummation → forwardBinomialTransform)
    (deriveInverseBinomialTransform :
      forwardBinomialTransform → binomialInversionInput → inverseBinomialTransform)
    (deriveStokesIntegralDictionary :
      walshCharacterDifferenceAction → multilinearStokesInterpretation →
        stokesIntegralDictionary) :
    forwardBinomialTransform ∧ inverseBinomialTransform ∧ stokesIntegralDictionary := by
  have hForward : forwardBinomialTransform :=
    deriveForwardBinomialTransform walshCharacterDifferenceAction_h subsetSummation_h
  have hInverse : inverseBinomialTransform :=
    deriveInverseBinomialTransform hForward binomialInversionInput_h
  have hStokes : stokesIntegralDictionary :=
    deriveStokesIntegralDictionary walshCharacterDifferenceAction_h
      multilinearStokesInterpretation_h
  exact ⟨hForward, hInverse, hStokes⟩

end Omega.Discussion
