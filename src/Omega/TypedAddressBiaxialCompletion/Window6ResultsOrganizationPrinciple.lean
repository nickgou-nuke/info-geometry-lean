import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Sentence roles used in the canonical window-6 results paragraph skeleton. -/
inductive ResultSentenceRole where
  | claim
  | evidence
  | statistic
  | mechanism
  deriving DecidableEq, Repr

/-- Canonical four-step paragraph skeleton for the first window-6 results paragraphs. -/
def window6ResultsParagraphRoles : List ResultSentenceRole :=
  [ResultSentenceRole.claim, ResultSentenceRole.evidence,
    ResultSentenceRole.statistic, ResultSentenceRole.mechanism]

/-- Paragraphs that have not passed the protocol gate remain placeholders. -/
def window6PreProtocolParagraphIsPlaceholder (protocolPassed : Bool) : Bool :=
  !protocolPassed

/-- A paragraph remains a placeholder exactly while the protocol has not passed. -/
theorem window6PreProtocolParagraphIsPlaceholder_iff_not_passed (protocolPassed : Bool) :
    window6PreProtocolParagraphIsPlaceholder protocolPassed = true ↔
      protocolPassed = false := by
  cases protocolPassed <;> simp [window6PreProtocolParagraphIsPlaceholder]

/-- The results paragraph contains each of the four declared sentence roles exactly once.
The `Nodup` conjunct rules out repeated roles, and the membership conjunct rules out omissions. -/
theorem paper_typed_address_biaxial_completion_window6_results_organization_principle :
    window6ResultsParagraphRoles.Nodup ∧
      ∀ role : ResultSentenceRole, role ∈ window6ResultsParagraphRoles := by
  constructor
  · simp [window6ResultsParagraphRoles]
  · intro role
    cases role <;> simp [window6ResultsParagraphRoles]

end Omega.TypedAddressBiaxialCompletion
