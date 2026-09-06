import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- A visible permutation and its lift/counting hypotheses yield the two stated lift laws. -/
theorem paper_op_algebra_fold_visible_permutation_lifts
    (visiblePermutation liftCriterion gaugeGroupCardinalityWitness : Prop)
    (liftExists_iff_fiberMultiplicityPreserved liftCount_eq_gaugeGroupCard : Prop)
    (visiblePermutation_h : visiblePermutation)
    (liftCriterion_h : liftCriterion)
    (gaugeGroupCardinalityWitness_h : gaugeGroupCardinalityWitness)
    (deriveLiftExists_iff_fiberMultiplicityPreserved :
      visiblePermutation → liftCriterion →
        liftExists_iff_fiberMultiplicityPreserved)
    (deriveLiftCount_eqGaugeGroupCard :
      visiblePermutation → liftCriterion → gaugeGroupCardinalityWitness →
        liftCount_eq_gaugeGroupCard) :
    liftExists_iff_fiberMultiplicityPreserved ∧ liftCount_eq_gaugeGroupCard := by
  exact
    ⟨deriveLiftExists_iff_fiberMultiplicityPreserved visiblePermutation_h liftCriterion_h,
      deriveLiftCount_eqGaugeGroupCard visiblePermutation_h liftCriterion_h
        gaugeGroupCardinalityWitness_h⟩

end Omega.OperatorAlgebra
