import Mathlib.Tactic

namespace Omega.Discussion

/-- A finite fold pushforward yields a positive circle measure, its Caratheodory--Herglotz
positivity, the Toeplitz PSD hierarchy, and the stated weak-limit audit implication. -/
theorem paper_discussion_horizon_measure_fold6_pushforward
    (finiteFoldPushforwardMeasure positiveCircleMeasure caratheodoryHerglotzPositivity
      toeplitzPsdHierarchy weakLimitExists weakLimitAuditInput : Prop)
    (packagePositiveCircleMeasure :
      finiteFoldPushforwardMeasure → positiveCircleMeasure)
    (deriveCaratheodoryHerglotzPositivity :
      positiveCircleMeasure → caratheodoryHerglotzPositivity)
    (deriveToeplitzPsdHierarchy :
      positiveCircleMeasure → caratheodoryHerglotzPositivity → toeplitzPsdHierarchy)
    (weakLimitFeedsAudit : weakLimitExists → weakLimitAuditInput)
    (hFiniteFoldPushforwardMeasure : finiteFoldPushforwardMeasure) :
    positiveCircleMeasure ∧ caratheodoryHerglotzPositivity ∧ toeplitzPsdHierarchy ∧
      (weakLimitExists → weakLimitAuditInput) := by
  have hMeasure : positiveCircleMeasure :=
    packagePositiveCircleMeasure hFiniteFoldPushforwardMeasure
  have hPositive : caratheodoryHerglotzPositivity :=
    deriveCaratheodoryHerglotzPositivity hMeasure
  exact ⟨hMeasure, hPositive, deriveToeplitzPsdHierarchy hMeasure hPositive,
    weakLimitFeedsAudit⟩

end Omega.Discussion
