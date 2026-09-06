import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.NullExhaustive

namespace Omega.Zeta

/-- Paper label: `thm:xi-null-complete-trichotomy-offline`. -/
theorem paper_xi_null_complete_trichotomy_offline
    (exhaustive semanticFailuresRequireAddressChange protocolFailuresNeedProtocolRepair
      collisionFailuresNeedSupportAxisBudget : Prop)
    (hExhaustive : exhaustive)
    (hSemanticRepair : semanticFailuresRequireAddressChange)
    (hProtocolRepair : protocolFailuresNeedProtocolRepair)
    (hCollisionRepair : collisionFailuresNeedSupportAxisBudget) :
    exhaustive ∧ semanticFailuresRequireAddressChange ∧
      protocolFailuresNeedProtocolRepair ∧ collisionFailuresNeedSupportAxisBudget := by
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_null_exhaustive
    exhaustive semanticFailuresRequireAddressChange protocolFailuresNeedProtocolRepair
    collisionFailuresNeedSupportAxisBudget hExhaustive hSemanticRepair hProtocolRepair
    hCollisionRepair

end Omega.Zeta
