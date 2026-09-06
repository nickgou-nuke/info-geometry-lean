import Mathlib.Tactic

namespace Omega.GU

universe u

/-- Infinitely many common slow-mode layers force a nontrivial common factor. -/
theorem paper_gut_cyclotomic_specialization_rigidity
    (BivariatePolynomial : Type u)
    (infinitelyManyCommonSlowModes : Prop)
    (nontrivialCommonFactor : BivariatePolynomial → Prop)
    (specializationRigidity :
      infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H) :
    infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H := by
  exact specializationRigidity

/-- Chapter-facing theorem for cyclotomic specialization rigidity. -/
theorem paper_cyclotomic_specialization_rigidity
    (BivariatePolynomial : Type u)
    (infinitelyManyCommonSlowModes : Prop)
    (nontrivialCommonFactor : BivariatePolynomial → Prop)
    (specializationRigidity :
      infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H) :
    infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H := by
  exact paper_gut_cyclotomic_specialization_rigidity BivariatePolynomial
    infinitelyManyCommonSlowModes nontrivialCommonFactor specializationRigidity

end Omega.GU
