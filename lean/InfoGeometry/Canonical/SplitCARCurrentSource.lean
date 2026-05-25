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

/-! ## Direct constructive closure (no witness wrapper in theorem statements) -/

/--
Direct source-side closure on the explicit charged-Fock current family:
truncation and full Heisenberg commutator law.
-/
theorem chargedFockSpace_current_constructive_J_trunc_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ l : Int in atTop,
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J l v = 0)
      ∧
    (∀ m n : Int,
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m).commutator
          ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else
        0) := by
  exact ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc,
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm⟩

/--
Direct existence theorem for a source current family `J` satisfying truncation
and the full Heisenberg commutator law.
-/
theorem chargedFockSpace_current_exists_J_trunc_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J : Int →
      VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α,
      (∀ v, ∀ᶠ l : Int in atTop, J l v = 0)
      ∧
      (∀ m n : Int,
        (J m).commutator (J n) =
          if m + n = 0 then
            (m : 𝕜) •
              (1 :
                VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                  VirasoroProject.ChargedFockSpace 𝕜 α)
          else
            0) := by
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
