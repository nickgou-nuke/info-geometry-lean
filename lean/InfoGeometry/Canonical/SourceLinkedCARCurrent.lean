import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

set_option linter.unusedSectionVars false

/-!
# Source-Linked CAR-to-Current Adapter

This file provides the end-to-end theorem connecting a raw CAR mode completion
with a source-faithful stabilized current adapter to Sugawara Virasoro.
-/

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCARCurrentSourceAdapter
open VirasoroProject

namespace InfoGeometry.Canonical.SourceLinkedCARCurrent

/--
End-to-end theorem: Raw CAR + adapter → Heisenberg → Sugawara Virasoro.
Given an adapter whose source is `C`, this theorem returns the induced Heisenberg
representation and its Sugawara stress-tensor Virasoro commutator.
-/
theorem rawCAR_to_SugawaraVirasoro_bridge
    {A : Type*} [Ring A] (C : RawCARModeCompletion A)
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (S : AdapterData 𝕜 A (VirasoroProject.ChargedFockSpace 𝕜 α))
    (hS : S.source = C) :
    ∃ (H : CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)),
      H.J = S.J ∧
      S.source = C ∧
      (∀ m n, (H.J m).commutator (H.J n) =
        if m + n = 0 then (m : 𝕜) • (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) else 0) ∧
      (∀ m n, (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
        (m - n) • H.sugawaraStressMode (m + n) +
          if m + n = 0 then (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α)) else 0) := by
  refine ⟨S.toCurrentHeisenbergRep, rfl, hS, ?_, ?_⟩
  · intro m n
    exact S.comm m n
  · intro m n
    simpa using (S.toCurrentHeisenbergRep.sugawaraStressMode_virasoroBracket m n)

end InfoGeometry.Canonical.SourceLinkedCARCurrent
