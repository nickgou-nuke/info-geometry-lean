import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.SplitCARCurrentSource

Source-side CAR-to-current witness boundary.

This file packages the data required to pass from a CAR source to the already
owned `CurrentHeisenbergRep` and downstream Sugawara bridge.

The constructive bridge packaging raw CAR data into a `SplitCARCurrentWitness` is closed
in `InfoGeometry.Canonical.ChargedFockSpaceFromRawCAR` via `chargedFockSpaceWitnessFromRawCAR`.
-/

namespace InfoGeometry.Canonical.SplitCARCurrentSource

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge

set_option synthInstance.maxHeartbeats 200000

/--
A CAR-to-current witness.

This is the exact package needed to build a `CurrentHeisenbergRep` once a
source-side construction has been proved.
-/
structure SplitCARCurrentWitness
    (𝕜 A V : Type*) [Field 𝕜] [CharZero 𝕜]
    [Ring A] [AddCommGroup V] [Module 𝕜 V] where
  /-- A raw CAR packet carried by the witness. -/
  source : RawCARModeCompletion A
  /-- The current modes on the carrier. -/
  J : Int → V →ₗ[𝕜] V
  /-- Local truncation for the current family. -/
  trunc : ∀ v, ∀ᶠ l : Int in atTop, J l v = 0
  /-- Heisenberg commutator law. -/
  comm :
    ∀ m n, (J m).commutator (J n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

namespace SplitCARCurrentWitness

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- Convert the witness into the repository's `CurrentHeisenbergRep`. -/
def toCurrentHeisenbergRep
    (W : SplitCARCurrentWitness 𝕜 A V) :
    CurrentHeisenbergRep 𝕜 V where
  J := W.J
  trunc := W.trunc
  comm := W.comm

/-- The converted Heisenberg representation preserves the witness fields and current law. -/
theorem toCurrentHeisenbergRep_readout
    (W : SplitCARCurrentWitness 𝕜 A V) :
    W.toCurrentHeisenbergRep.J = W.J ∧
      (∀ m n, (W.toCurrentHeisenbergRep.J m).commutator (W.toCurrentHeisenbergRep.J n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) := by
  refine ⟨rfl, ?_⟩
  intro m n
  exact W.comm m n

end SplitCARCurrentWitness

/--
Constructive existence theorem: Every raw CAR mode completion `C` induces a valid
Heisenberg current representation on `ChargedFockSpace 𝕜 α`.
-/
theorem chargedFockSpace_current_representation_exists
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ (J : Int → VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α),
      (∀ v, ∀ᶠ l : Int in atTop, J l v = 0) ∧
      (∀ m n, (J m).commutator (J n) =
        if m + n = 0 then
          (m : 𝕜) • (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)
        else 0) := by
  refine ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
  exact ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc,
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm⟩

/--
Concrete central-mode readout from the explicit charged-Fock current family:
`[J₁, J₋₁] = 1 • id`.
-/
theorem chargedFockSpace_current_commutator_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J 1).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (-1))
      =
    (1 : 𝕜) •
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm 1 (-1)

/--
Off-resonance current commutator vanishes:
if `m + n ≠ 0`, then `[J_m, J_n] = 0`.
-/
theorem chargedFockSpace_current_commutator_zero_of_add_ne_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int)
    (h : m + n ≠ 0) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n)
      =
      (0 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa [h] using (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

/--
Resonant current commutator is central:
if `m + n = 0`, then `[J_m, J_n] = m • id`.
-/
theorem chargedFockSpace_current_commutator_central_of_add_eq_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int)
    (h : m + n = 0) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n)
      =
      (m : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa [h] using (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

end InfoGeometry.Canonical.SplitCARCurrentSource
