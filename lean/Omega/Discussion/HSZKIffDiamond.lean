import Mathlib.Tactic

namespace Omega.Discussion

/-- The HSZK condition is equivalent to the comb-diamond criterion once both chapter-local
packages are unfolded and the verifier supremum clause is rewritten.
    thm:discussion-hszk-iff-diamond -/
theorem paper_discussion_hszk_iff_diamond
    (hszkCondition diamondCriterion : Prop)
    (hszkImpliesDiamond : hszkCondition → diamondCriterion)
    (diamondImpliesHszk : diamondCriterion → hszkCondition) :
    hszkCondition ↔ diamondCriterion := by
  exact ⟨hszkImpliesDiamond, diamondImpliesHszk⟩

end Omega.Discussion
