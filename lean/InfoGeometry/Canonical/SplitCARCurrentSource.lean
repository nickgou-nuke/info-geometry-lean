import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.SplitCARCurrentSource

Source-side CAR-to-current witness boundary.

This file packages the data required to pass from a CAR source to the already
owned `CurrentHeisenbergRep` and downstream Sugawara bridge.

It does not claim that split-Clifford data itself already provides such a
witness. The actual split-source construction theorem remains open debt.
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

/-- Any such witness yields a `CurrentHeisenbergRep`. -/
theorem toCurrentHeisenbergRep_nonempty
    (W : SplitCARCurrentWitness 𝕜 A V) :
    Nonempty (CurrentHeisenbergRep 𝕜 V) :=
  ⟨W.toCurrentHeisenbergRep⟩

end SplitCARCurrentWitness

/-
Concrete example witness
------------------------
The repo already owns the Heisenberg current witness for the charged Fock
module.  We package that concrete witness together with the raw CAR source
packet used elsewhere in the current/Sugawara corridor.
-/

noncomputable def chargedFockSpaceSplitCARCurrentWitness
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α) where
  source :=
    exteriorFockRawCAR
      (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜)
      (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis 𝕜)
  J := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
  trunc := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  comm := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_J
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n :=
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc :=
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm :=
  rfl

/-- The concrete charged-Fock CAR witness is nonempty. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  ⟨chargedFockSpaceSplitCARCurrentWitness 𝕜 α⟩

/-- The concrete charged-Fock CAR witness canonically yields a Sugawara morphism. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep :=
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation :=
  rfl

/-- The concrete charged-Fock CAR witness also yields the packaged Sugawara surface. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  ⟨chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α⟩

end InfoGeometry.Canonical.SplitCARCurrentSource
