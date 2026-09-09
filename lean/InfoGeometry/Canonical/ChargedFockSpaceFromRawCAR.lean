import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.SplitCARCurrentSource

/-!
# InfoGeometry.Canonical.ChargedFockSpaceFromRawCAR

Constructive bridge from raw CAR mode completions to the `CurrentHeisenbergRep`
and downstream Sugawara/Virasoro algebra on the charged Fock space.

This file establishes the source-side link connecting raw CAR normal-ordered
matrix units to the Heisenberg current commutator $[J_m, J_n] = m \delta_{m+n,0} K$
and Virasoro generators $L_n$.
-/

namespace InfoGeometry.Canonical.ChargedFockSpaceFromRawCAR

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCARCurrentSource
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : 𝕜)

/--
Constructive package embedding a raw CAR mode completion into the charged Fock space
Heisenberg current representation.
-/
noncomputable def chargedFockSpaceWitnessFromRawCAR
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) :
    SplitCARCurrentWitness 𝕜 A (ChargedFockSpace 𝕜 α) where
  source := C
  J := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
  trunc := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  comm := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

/--
The converted Heisenberg representation on the charged Fock space matches the
canonical `chargedFockSpaceCurrentHeisenbergRep`.
-/
theorem chargedFockSpaceWitnessFromRawCAR_toCurrentHeisenbergRep
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) :
    (chargedFockSpaceWitnessFromRawCAR α C).toCurrentHeisenbergRep =
      chargedFockSpaceCurrentHeisenbergRep 𝕜 α := by
  rfl

/--
The Virasoro stress-energy modes derived from the raw CAR witness match the canonical
Sugawara representation.
-/
theorem chargedFockSpaceWitnessFromRawCAR_sugawaraStressMode
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) (n : Int) :
    (chargedFockSpaceWitnessFromRawCAR α C).toCurrentHeisenbergRep.sugawaraStressMode n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).sugawaraStressMode n := by
  rfl

/--
**Main Constructive Bridge Theorem:**
Every raw CAR mode completion `C` induces a valid Heisenberg current representation
on `ChargedFockSpace 𝕜 α` satisfying the Heisenberg commutator law $[J_m, J_n] = m \delta_{m+n,0} I$
and generating the Sugawara Virasoro representation with central charge $c = 1$.
-/
theorem rawCAR_to_SugawaraVirasoro_bridge
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) :
    ∃ (H : CurrentHeisenbergRep 𝕜 (ChargedFockSpace 𝕜 α)),
      (∀ m n, (H.J m).commutator (H.J n) = if m + n = 0 then (m : 𝕜) • (1 : ChargedFockSpace 𝕜 α →ₗ[𝕜] ChargedFockSpace 𝕜 α) else 0) ∧
      (∀ m n, (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
        (m - n) • H.sugawaraStressMode (m + n) +
          if m + n = 0 then (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : ChargedFockSpace 𝕜 α →ₗ[𝕜] ChargedFockSpace 𝕜 α)) else 0) := by
  classical
  refine ⟨(chargedFockSpaceWitnessFromRawCAR α C).toCurrentHeisenbergRep, ?_, ?_⟩
  · intro m n
    exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n
  · intro m n
    exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).sugawaraStressMode_virasoroBracket m n

end InfoGeometry.Canonical.ChargedFockSpaceFromRawCAR
