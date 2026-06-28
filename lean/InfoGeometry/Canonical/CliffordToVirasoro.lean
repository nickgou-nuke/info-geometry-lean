import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.External.Virasoro.FockSpaceSugawara

/-!
# Clifford-to-Virasoro Boundary Bridge

This file keeps the Clifford-to-Virasoro boundary on the repository's proved
interfaces.

The safe source object is a `CurrentHeisenbergRep`: a current family with local
truncation and the Heisenberg commutator law.  From that data, the existing
`SplitCliffordHeisenbergBridge` and `CurrentSugawaraBridge` produce the
Sugawara/Virasoro representation.  The charged Fock specialization is
constructed from the already proved `chargedFockSpaceCurrentHeisenbergRep`.

This file does not assert an isomorphism between `SplitCliffordInfinity` and a
Fock space.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordToVirasoro

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

/-! ### 1. Current witness packaging -/

/-- Package an already proved Heisenberg current representation as a split-Clifford witness. -/
def construct_heisenberg_witness
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V) :
    SplitCliffordHeisenbergWitness 𝕜 V where
  J := H.J
  trunc := H.trunc
  comm := H.comm

@[simp] theorem construct_heisenberg_witness_J
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) :
    (construct_heisenberg_witness H).J n = H.J n :=
  rfl

/-! ### 2. Pipeline theorem -/

/--
Any proved Heisenberg current representation gives the split-current witness,
the packaged current interface, the Sugawara morphism, and the Virasoro
representation.
-/
noncomputable def clifford_current_to_virasoro_sugawara
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V) :
    SplitCliffordHeisenbergWitness 𝕜 V ×
      CurrentHeisenbergRep 𝕜 V ×
        CurrentSugawaraMorphism 𝕜 V ×
          (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) := by
  let W : SplitCliffordHeisenbergWitness 𝕜 V := construct_heisenberg_witness H
  exact
    ⟨W, H, splitClifford_to_currentSugawaraMorphism W,
      splitClifford_to_sugawaraRepresentation W⟩

/-! ### 3. Charged Fock specialization -/

/-- The charged Fock space carries the split-current witness induced by its Heisenberg modes. -/
def charged_fock_space_witness
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitCliffordHeisenbergWitness 𝕜 (ChargedFockSpace 𝕜 α) :=
  construct_heisenberg_witness (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- The charged Fock witness has the expected current readout. -/
theorem charged_fock_space_witness_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (charged_fock_space_witness 𝕜 α).J = (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
      ∧ (charged_fock_space_witness 𝕜 α).trunc =
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
      ∧ ∀ m n,
          ((charged_fock_space_witness 𝕜 α).J m).commutator
              ((charged_fock_space_witness 𝕜 α).J n) =
            if m + n = 0 then (m : 𝕜) •
              (1 : ChargedFockSpace 𝕜 α →ₗ[𝕜] ChargedFockSpace 𝕜 α) else 0 := by
  exact ⟨rfl, rfl, (charged_fock_space_witness 𝕜 α).comm⟩

/-- The full current/Sugawara/Virasoro pipeline works for the charged Fock space. -/
noncomputable def charged_fock_space_full_pipeline
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitCliffordHeisenbergWitness 𝕜 (ChargedFockSpace 𝕜 α) ×
      CurrentHeisenbergRep 𝕜 (ChargedFockSpace 𝕜 α) ×
        CurrentSugawaraMorphism 𝕜 (ChargedFockSpace 𝕜 α) ×
          (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
            (ChargedFockSpace 𝕜 α →ₗ[𝕜] ChargedFockSpace 𝕜 α)) :=
  clifford_current_to_virasoro_sugawara
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

end InfoGeometry.Canonical.CliffordToVirasoro
