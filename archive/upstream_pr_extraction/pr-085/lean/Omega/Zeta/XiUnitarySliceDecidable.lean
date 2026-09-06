import Omega.CircleDimension.UnitarySliceDecidable
import Omega.Zeta.XiNullCompleteTrichotomyOffline

namespace Omega.Zeta

open Omega.CircleDimension.UnitarySliceDecidable

/-- Paper-facing `xi` wrapper over the unitary-slice decidability criterion: the existing finite
positive/readout witness package decides addressability on the unitary slice, and the offline
null-trichotomy wrapper supplies the three `NULL` failure modes.
    cor:xi-unitary-slice-decidable -/
theorem paper_xi_unitary_slice_decidable :
    Omega.CircleDimension.UnitarySliceDecidable.paper_cdim_unitary_slice_decidable ∧
      (∀ (exhaustive semanticFailuresRequireAddressChange protocolFailuresNeedProtocolRepair
          collisionFailuresNeedSupportAxisBudget : Prop)
          (hExhaustive : exhaustive)
          (hSemanticRepair : semanticFailuresRequireAddressChange)
          (hProtocolRepair : protocolFailuresNeedProtocolRepair)
          (hCollisionRepair : collisionFailuresNeedSupportAxisBudget),
        exhaustive ∧ semanticFailuresRequireAddressChange ∧
          protocolFailuresNeedProtocolRepair ∧ collisionFailuresNeedSupportAxisBudget) := by
  refine ⟨?_, ?_⟩
  · intro State Ref Value _ Adm Vis Γ hΓ p r _ _
    exact paper_cdim_unitary_slice_decidable_package Adm Vis Γ hΓ
  · intro exhaustive semanticFailuresRequireAddressChange protocolFailuresNeedProtocolRepair
      collisionFailuresNeedSupportAxisBudget hExhaustive hSemanticRepair hProtocolRepair
      hCollisionRepair
    exact paper_xi_null_complete_trichotomy_offline exhaustive
      semanticFailuresRequireAddressChange protocolFailuresNeedProtocolRepair
      collisionFailuresNeedSupportAxisBudget hExhaustive hSemanticRepair hProtocolRepair
      hCollisionRepair

end Omega.Zeta
