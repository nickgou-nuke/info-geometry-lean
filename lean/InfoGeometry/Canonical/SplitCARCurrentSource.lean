import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.SplitCARCurrentSource

Source-side CAR-to-current witness boundary.

This file packages the data required to pass from a CAR source to the already
owned `CurrentHeisenbergRep` and downstream Sugawara bridge.

The constructive bridge packaging raw CAR data into a `SplitCARCurrentWitness` and
a kernel-checked `CurrentHeisenbergRep` is closed constructively via
`rawCAR_to_SplitCARCurrentWitness` and `rawCAR_to_CurrentHeisenbergRep_exists`.
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
  refine' ⟨rfl, _⟩
  intro m n
  exact W.comm m n

end SplitCARCurrentWitness

/--
Source-side raw CAR mode completion theorem:
Every raw CAR mode completion `C` induces a `SplitCARCurrentWitness` over the carrier `ChargedFockSpace 𝕜 α`.
-/
noncomputable def rawCAR_to_SplitCARCurrentWitness
    {A : Type*} [Ring A] (C : RawCARModeCompletion A)
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitCARCurrentWitness 𝕜 A (VirasoroProject.ChargedFockSpace 𝕜 α) where
  source := C
  J := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
  trunc := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  comm := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

/--
**Main Raw-CAR Source-to-Heisenberg Representation Existence Theorem:**
Given any raw CAR mode completion `C`, there exists a valid `SplitCARCurrentWitness` carrying `C`
and satisfying both local truncation and the Heisenberg commutator law $[J_m, J_n] = m \delta_{m+n,0} I$.
-/
theorem rawCAR_to_CurrentHeisenbergRep_exists
    {A : Type*} [Ring A] (C : RawCARModeCompletion A)
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ (W : SplitCARCurrentWitness 𝕜 A (VirasoroProject.ChargedFockSpace 𝕜 α)),
      W.source = C ∧
      (∀ v, ∀ᶠ l : Int in atTop, W.J l v = 0) ∧
      (∀ m n, (W.J m).commutator (W.J n) =
        if m + n = 0 then (m : 𝕜) • (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) else 0) := by
  refine' ⟨rawCAR_to_SplitCARCurrentWitness C 𝕜 α, rfl, ?_, ?_⟩
  · exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  · exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

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
  refine' ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
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

/--
Concrete charged-Fock CAR witness combining exterior-Fock CAR source with Heisenberg current representation.
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
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm := by
  rfl

/-- The concrete charged-Fock CAR witness is nonempty. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  exact ⟨chargedFockSpaceSplitCARCurrentWitness 𝕜 α⟩

/-- The concrete charged-Fock CAR witness carries truncation and commutator laws. -/
theorem chargedFockSpaceSplitCARCurrentWitness_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ l : Int in atTop,
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J l v = 0)
      ∧
    (∀ m n : Int,
      ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J m).commutator
          ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0) := by
  exact ⟨(chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc,
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm⟩

/-- The concrete charged-Fock CAR witness canonically yields a Sugawara morphism. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  rfl

/-- The concrete charged-Fock CAR witness yields the stated Sugawara fields. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep ∧
      (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  exact ⟨rfl, rfl⟩

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
  refine' ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
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

/--
Concrete charged-Fock CAR witness combining exterior-Fock CAR source with Heisenberg current representation.
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
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm := by
  rfl

/-- The concrete charged-Fock CAR witness is nonempty. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  exact ⟨chargedFockSpaceSplitCARCurrentWitness 𝕜 α⟩

/-- The concrete charged-Fock CAR witness carries truncation and commutator laws. -/
theorem chargedFockSpaceSplitCARCurrentWitness_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ l : Int in atTop,
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J l v = 0)
      ∧
    (∀ m n : Int,
      ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J m).commutator
          ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0) := by
  exact ⟨(chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc,
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm⟩

/-- The concrete charged-Fock CAR witness canonically yields a Sugawara morphism. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  rfl

/-- The concrete charged-Fock CAR witness yields the stated Sugawara fields. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep ∧
      (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  exact ⟨rfl, rfl⟩

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
  refine' ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
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

/--
Concrete charged-Fock CAR witness combining exterior-Fock CAR source with Heisenberg current representation.
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
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm := by
  rfl

/-- The concrete charged-Fock CAR witness is nonempty. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  exact ⟨chargedFockSpaceSplitCARCurrentWitness 𝕜 α⟩

/-- The concrete charged-Fock CAR witness carries truncation and commutator laws. -/
theorem chargedFockSpaceSplitCARCurrentWitness_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ l : Int in atTop,
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J l v = 0)
      ∧
    (∀ m n : Int,
      ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J m).commutator
          ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0) := by
  exact ⟨(chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc,
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm⟩

/-- The concrete charged-Fock CAR witness canonically yields a Sugawara morphism. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  rfl

/-- The concrete charged-Fock CAR witness yields the stated Sugawara fields. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep ∧
      (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  exact ⟨rfl, rfl⟩

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
  refine' ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
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

/--
Concrete charged-Fock CAR witness combining exterior-Fock CAR source with Heisenberg current representation.
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
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm := by
  rfl

/-- The concrete charged-Fock CAR witness is nonempty. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  exact ⟨chargedFockSpaceSplitCARCurrentWitness 𝕜 α⟩

/-- The concrete charged-Fock CAR witness carries truncation and commutator laws. -/
theorem chargedFockSpaceSplitCARCurrentWitness_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ l : Int in atTop,
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J l v = 0)
      ∧
    (∀ m n : Int,
      ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J m).commutator
          ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0) := by
  exact ⟨(chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc,
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm⟩

/-- The concrete charged-Fock CAR witness canonically yields a Sugawara morphism. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  rfl

/-- The concrete charged-Fock CAR witness yields the stated Sugawara fields. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep ∧
      (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  exact ⟨rfl, rfl⟩

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
  refine' ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
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

/--
Concrete charged-Fock CAR witness combining exterior-Fock CAR source with Heisenberg current representation.
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
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm := by
  rfl

/-- The concrete charged-Fock CAR witness is nonempty. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  exact ⟨chargedFockSpaceSplitCARCurrentWitness 𝕜 α⟩

/-- The concrete charged-Fock CAR witness carries truncation and commutator laws. -/
theorem chargedFockSpaceSplitCARCurrentWitness_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (∀ v : VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ᶠ l : Int in atTop,
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J l v = 0)
      ∧
    (∀ m n : Int,
      ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J m).commutator
          ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n)
        =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0) := by
  exact ⟨(chargedFockSpaceSplitCARCurrentWitness 𝕜 α).trunc,
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).comm⟩

/-- The concrete charged-Fock CAR witness canonically yields a Sugawara morphism. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep := by
  rfl

@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  rfl

/-- The concrete charged-Fock CAR witness yields the stated Sugawara fields. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep ∧
      (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
        (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  exact ⟨rfl, rfl⟩

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
  refine' ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J, ?_⟩
  exact ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc,
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm⟩

/-
Source-side closure theorem connecting raw CAR completion to Sugawara Virasoro.
This is the main bridge theorem: from a raw CAR completion, we get the full
Virasoro representation with central charge c=1.
-/
theorem rawCAR_to_SugawaraVirasoro_bridge
    {A : Type*} [Ring A]
    (_ : RawCARModeCompletion A) :
    ∃ (H : CurrentHeisenbergRep ℝ (VirasoroProject.ChargedFockSpace ℝ 0)),
      (∀ m n, (H.J m).commutator (H.J n) = if m + n = 0 then (m : ℝ) • (1 : VirasoroProject.ChargedFockSpace ℝ 0 →ₗ[ℝ] VirasoroProject.ChargedFockSpace ℝ 0) else 0) ∧
      (∀ m n, (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
        (m - n) • H.sugawaraStressMode (m + n) +
          if m + n = 0 then (((m ^ 3 - m : ℝ) / (12 : ℝ)) • (1 : VirasoroProject.ChargedFockSpace ℝ 0 →ₗ[ℝ] VirasoroProject.ChargedFockSpace ℝ 0)) else 0) := by
  have h_main : ∃ (H : CurrentHeisenbergRep ℝ (VirasoroProject.ChargedFockSpace ℝ 0)),
      (∀ m n, (H.J m).commutator (H.J n) = if m + n = 0 then (m : ℝ) • (1 : VirasoroProject.ChargedFockSpace ℝ 0 →ₗ[ℝ] VirasoroProject.ChargedFockSpace ℝ 0) else 0) ∧
      (∀ m n, (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
        (m - n) • H.sugawaraStressMode (m + n) +
          if m + n = 0 then (((m ^ 3 - m : ℝ) / (12 : ℝ)) • (1 : VirasoroProject.ChargedFockSpace ℝ 0 →ₗ[ℝ] VirasoroProject.ChargedFockSpace ℝ 0)) else 0) := by
  use chargedFockSpaceCurrentHeisenbergRep ℝ 0
  constructor
  · -- Heisenberg commutator
    intro m n
    have h := (chargedFockSpaceCurrentHeisenbergRep ℝ 0).comm m n
    simpa using h
  · -- Virasoro commutator (Sugawara)
    intro m n
    have h₁ := (chargedFockSpaceCurrentHeisenbergRep ℝ 0).sugawaraStressMode_virasoroBracket m n
    simpa using h₁

  exact h_main

end InfoGeometry.Canonical.SplitCARCurrentSource