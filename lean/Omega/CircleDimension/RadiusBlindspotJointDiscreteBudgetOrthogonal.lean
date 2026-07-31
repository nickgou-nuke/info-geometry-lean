import Mathlib.Tactic
import Omega.CircleDimension.AddressLedgerJointBudgetLowerBound

namespace Omega.CircleDimension

/-- The boundary-layer blindspot budget and the address-ledger joint budget give two orthogonal
necessary conditions.
    cor:cdim-radius-blindspot-and-joint-discrete-budget-orthogonal -/
theorem paper_cdim_radius_blindspot_and_joint_discrete_budget_orthogonal
    {radiusBlindspotNecessary addressLedgerNecessary : Prop}
    (hRadius : radiusBlindspotNecessary)
    (hAddress : addressLedgerNecessary) :
    radiusBlindspotNecessary ∧ addressLedgerNecessary :=
  ⟨hRadius, hAddress⟩

end Omega.CircleDimension
