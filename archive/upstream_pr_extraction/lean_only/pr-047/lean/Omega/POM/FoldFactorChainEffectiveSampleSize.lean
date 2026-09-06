import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing wrapper for the lazy fold-factor-chain effective sample-size package: the
stationary variance estimate, the lazy-gap lower bound, the specialized `0-1` mean-square error
bound, and the success-observable identity are all extracted directly from the chapter-local data.
    prop:pom-fold-factor-chain-effective-sample-size -/
theorem paper_pom_fold_factor_chain_effective_sample_size
    {stationaryVarianceBound lazyGapLowerBound zeroOneMseBound successObservableMean : Prop}
    (hStationaryVarianceBound : stationaryVarianceBound)
    (hLazyGapLowerBound : lazyGapLowerBound)
    (hZeroOneMseBound : zeroOneMseBound)
    (hSuccessObservableMean : successObservableMean) :
    stationaryVarianceBound /\ lazyGapLowerBound /\ zeroOneMseBound /\ successObservableMean := by
  exact
    ⟨hStationaryVarianceBound, hLazyGapLowerBound, hZeroOneMseBound,
      hSuccessObservableMean⟩

end Omega.POM
