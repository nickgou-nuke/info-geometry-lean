import Omega.GU.CyclotomicSpecializationRigidity

namespace Omega.GU

universe u

/-- A trivial residual gcd rules out an extra gcd occurring at infinitely many levels. -/
theorem paper_gut_cyclotomic_gcd_stability
    (BivariatePolynomial : Type u)
    (nontrivialCommonFactor : BivariatePolynomial → Prop)
    (infinitelyManyCommonSlowModes residualGcdTrivial extraGcdAtInfinitelyManyLevels : Prop)
    (specializationRigidity :
      infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H)
    (extraGcdForcesInfinitelyManyCommonSlowModes :
      extraGcdAtInfinitelyManyLevels → infinitelyManyCommonSlowModes)
    (residualGcdExcludesNontrivialCommonFactor :
      residualGcdTrivial → ¬ ∃ H : BivariatePolynomial, nontrivialCommonFactor H) :
    residualGcdTrivial → ¬ extraGcdAtInfinitelyManyLevels := by
  intro hResidual hExtra
  obtain ⟨H, hH⟩ :=
    paper_gut_cyclotomic_specialization_rigidity BivariatePolynomial
      infinitelyManyCommonSlowModes nontrivialCommonFactor specializationRigidity
      (extraGcdForcesInfinitelyManyCommonSlowModes hExtra)
  exact (residualGcdExcludesNontrivialCommonFactor hResidual) ⟨H, hH⟩

end Omega.GU
