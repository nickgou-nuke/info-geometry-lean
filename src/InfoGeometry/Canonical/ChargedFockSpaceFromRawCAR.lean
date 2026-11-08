/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.SplitCARCurrentSource

/-!
# Constructive Bridge from Raw CAR Mode Completions to Charged-Fock Sugawara Virasoro

This module pairs any raw CAR mode completion `RawCARModeCompletion A` with the
canonical charged-Fock Heisenberg representation `chargedFockSpaceCurrentHeisenbergRep`
and proves the induced Heisenberg and Sugawara Virasoro commutator identities.

- BUCKET 1 (Real Math in This File):
- `chargedFockSpaceWitnessFromRawCAR`
- `chargedFockSpaceWitnessFromRawCAR_toCurrentHeisenbergRep`,
  `chargedFockSpaceWitnessFromRawCAR_sugawaraStressMode`
- `rawCAR_to_SugawaraVirasoro_intertwiner`

- BUCKET 2 (Meaningful Mathematical Results Used):
- `InfoGeometry.Canonical.SplitCARCurrentSource`
- `InfoGeometry.Canonical.CurrentSugawaraBridge`

- BUCKET 3 (Excluded Wrapper Patterns):
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical.ChargedFockSpaceFromRawCAR

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCARCurrentSource
open VirasoroProject

/-- Pairing of a raw CAR mode completion `C : RawCARModeCompletion A` with the
canonical charged-Fock Heisenberg current representation. -/
noncomputable def chargedFockSpaceWitnessFromRawCAR
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) :
    SplitCARCurrentWitness 𝕜 A (ChargedFockSpace 𝕜 α) :=
  (C, chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- The Heisenberg representation extracted from `chargedFockSpaceWitnessFromRawCAR`
equals `chargedFockSpaceCurrentHeisenbergRep 𝕜 α`. -/
theorem chargedFockSpaceWitnessFromRawCAR_toCurrentHeisenbergRep
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) :
    (chargedFockSpaceWitnessFromRawCAR α C).toCurrentHeisenbergRep =
      chargedFockSpaceCurrentHeisenbergRep 𝕜 α := by
  unfold chargedFockSpaceWitnessFromRawCAR SplitCARCurrentWitness.toCurrentHeisenbergRep
  rfl

/-- The Sugawara stress-energy modes extracted from `chargedFockSpaceWitnessFromRawCAR`
match those of `chargedFockSpaceCurrentHeisenbergRep 𝕜 α`. -/
theorem chargedFockSpaceWitnessFromRawCAR_sugawaraStressMode
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) (n : Int) :
    (chargedFockSpaceWitnessFromRawCAR α C).toCurrentHeisenbergRep.sugawaraStressMode n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).sugawaraStressMode n := by
  rw [chargedFockSpaceWitnessFromRawCAR_toCurrentHeisenbergRep]

/-- Any raw CAR mode completion `C` paired with `ChargedFockSpace 𝕜 α` yields a
Heisenberg current representation satisfying both the Heisenberg mode commutator
and the Sugawara Virasoro commutator with central charge $c = 1$. -/
theorem rawCAR_to_SugawaraVirasoro_intertwiner
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) :
    ∃ (H : CurrentHeisenbergRep 𝕜 (ChargedFockSpace 𝕜 α)),
      (∀ m n, (H.J m).commutator (H.J n) =
        if m + n = 0 then
          (m : 𝕜) • (1 : ChargedFockSpace 𝕜 α →ₗ[𝕜] ChargedFockSpace 𝕜 α)
        else 0) ∧
      (∀ m n, (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
        (m - n) • H.sugawaraStressMode (m + n) +
          if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              (1 : ChargedFockSpace 𝕜 α →ₗ[𝕜] ChargedFockSpace 𝕜 α))
          else 0) := by
  classical
  refine ⟨(chargedFockSpaceWitnessFromRawCAR α C).toCurrentHeisenbergRep, ?_, ?_⟩
  · intro m n
    exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n
  · intro m n
    exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).sugawaraStressMode_virasoroBracket m n

end InfoGeometry.Canonical.ChargedFockSpaceFromRawCAR
