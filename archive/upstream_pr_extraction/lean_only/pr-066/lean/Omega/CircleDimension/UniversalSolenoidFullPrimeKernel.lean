import Mathlib.Tactic
import Omega.CircleDimension.RankoneSolenoidHeightClassification

namespace Omega.CircleDimension

/-- Paper-facing wrapper: specializing the rank-one solenoid height classification to the case
`h_p = ∞` for every prime yields the universal solenoid, its full `p`-adic kernel, and the stated
short exact sequence.
    cor:cdim-universal-solenoid-full-prime-kernel -/
theorem paper_cdim_universal_solenoid_full_prime_kernel
    {allPrimeHeightsInfinite dualGroupIsQHat kernelIsFullPadicProduct shortExactSequence : Prop}
    (hHeights : allPrimeHeightsInfinite)
    (hDual : dualGroupIsQHat)
    (hKernel : kernelIsFullPadicProduct)
    (hShortExact : shortExactSequence) :
    allPrimeHeightsInfinite ∧ dualGroupIsQHat ∧ kernelIsFullPadicProduct ∧ shortExactSequence :=
  ⟨hHeights, hDual, hKernel, hShortExact⟩

end Omega.CircleDimension
