import Mathlib.Tactic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
theorem paper_xi_real_input40_logM_infty_truncation_bound
    (rootBracket logFactorBound tailComparison explicitTailBound absoluteConvergence : Prop)
    (rootBracket_h : rootBracket)
    (deriveLogFactorBound : rootBracket → logFactorBound)
    (deriveTailComparison : rootBracket → logFactorBound → tailComparison)
    (deriveExplicitTailBound :
      rootBracket → logFactorBound → tailComparison → explicitTailBound)
    (deriveAbsoluteConvergence :
      rootBracket → logFactorBound → tailComparison → explicitTailBound → absoluteConvergence) :
    rootBracket ∧ logFactorBound ∧ tailComparison ∧
      explicitTailBound ∧ absoluteConvergence := by
  have hLog : logFactorBound := deriveLogFactorBound rootBracket_h
  have hTail : tailComparison := deriveTailComparison rootBracket_h hLog
  have hBound : explicitTailBound := deriveExplicitTailBound rootBracket_h hLog hTail
  exact ⟨rootBracket_h, hLog, hTail, hBound,
    deriveAbsoluteConvergence rootBracket_h hLog hTail hBound⟩

end Omega.Zeta
