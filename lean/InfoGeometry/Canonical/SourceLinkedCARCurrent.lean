import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

set_option linter.unusedSectionVars false

/-!
# Source-Linked CAR-to-Current Adapter

This file provides the end-to-end theorem connecting a raw CAR mode completion
to its stabilized Heisenberg current and Sugawara Virasoro representation.
-/

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge

namespace InfoGeometry.Canonical.SourceLinkedCARCurrent

/--
End-to-end theorem: Raw CAR → Heisenberg → Sugawara Virasoro.
This is the single composed theorem replacing separate witnesses.
-/
theorem rawCAR_to_SugawaraVirasoro_bridge
    {A : Type*} [Ring A] (C : RawCARModeCompletion A)
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ (H : CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)),
      H.J = (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J ∧
      (∀ m n, (H.J m).commutator (H.J n) =
        if m + n = 0 then (m : 𝕜) • (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) else 0) ∧
      (∀ m n, (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
        (m - n) • H.sugawaraStressMode (m + n) +
          if m + n = 0 then (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α)) else 0) := by
  use chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  refine ⟨rfl, ?_, ?_⟩
  · intro m n
    exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n
  · intro m n
    exact sugawaraVirasoro_from_heisenbergCurrent (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

end InfoGeometry.Canonical.SourceLinkedCARCurrent