import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldCriticalCapacityThreephaseLaw

open scoped goldenRatio

namespace Omega.Conclusion

/-- The existing three-phase law supplies the two exact boundary values of the full inversion
threshold. -/
theorem paper_conclusion_binfold_full_inversion_golden_threshold :
    binfoldCriticalCapacityThreephaseLaw (1 / Real.goldenRatio) =
        Real.goldenRatio / Real.sqrt 5 ∧
      binfoldCriticalCapacityThreephaseLaw 1 = 2 / Real.sqrt 5 := by
  have hthreePhase := paper_conclusion_binfold_critical_capacity_threephase_law
  exact ⟨hthreePhase.2.2.2.1, hthreePhase.2.2.2.2⟩

end Omega.Conclusion
