import Omega.Folding.MomentSum

namespace Omega.POM

/-- Paper-facing wrapper for the oracle Rényi-pressure failure estimate: first derive the
finite-volume failure bound from the `momentSum` normalization and the pointwise bound, then use
the pressure input to package the limsup inequality and the resulting error-exponent lower bound.
    thm:pom-oracle-renyi-pressure-failure-bound -/
theorem paper_pom_oracle_renyi_pressure_failure_bound
    (q : Nat) (Sq : Nat → Nat)
    (hSq : Sq = Omega.momentSum q)
    {failureBound pressureLimsupBound errorExponentLowerBound
        pointwisePositivePartBound normalizedQuantityRewrite pressureLimit : Prop}
    (hPointwisePositivePartBound : pointwisePositivePartBound)
    (hNormalizedQuantityRewrite : normalizedQuantityRewrite)
    (hPressureLimit : pressureLimit)
    (deriveFailureBound :
      Sq = Omega.momentSum q → pointwisePositivePartBound →
        normalizedQuantityRewrite → failureBound)
    (derivePressureLimsupBound : failureBound → pressureLimit → pressureLimsupBound)
    (deriveErrorExponentLowerBound :
      pressureLimsupBound → pressureLimit → errorExponentLowerBound) :
    And failureBound (And pressureLimsupBound errorExponentLowerBound) := by
  have hFailure : failureBound :=
    deriveFailureBound hSq hPointwisePositivePartBound hNormalizedQuantityRewrite
  have hLimsup : pressureLimsupBound :=
    derivePressureLimsupBound hFailure hPressureLimit
  have hExponent : errorExponentLowerBound :=
    deriveErrorExponentLowerBound hLimsup hPressureLimit
  exact ⟨hFailure, hLimsup, hExponent⟩

end Omega.POM
