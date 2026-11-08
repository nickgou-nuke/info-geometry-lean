/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Source-Side CAR-to-Current Heisenberg Representation Bridge

This module pairs a raw CAR mode completion `RawCARModeCompletion A` with a
`CurrentHeisenbergRep 𝕜 V`, defines its projection into `CurrentHeisenbergRep`
and `CurrentSugawaraMorphism`, and proves the concrete charged-Fock CAR current
truncation and commutator laws.

- BUCKET 1 (Real Math in This File):
  - `SplitCARCurrentWitness`, `SplitCARCurrentWitness.source`,
    `SplitCARCurrentWitness.J`, `SplitCARCurrentWitness.trunc`, `SplitCARCurrentWitness.comm`
  - `SplitCARCurrentWitness.toCurrentHeisenbergRep`,
    `SplitCARCurrentWitness.toCurrentHeisenbergRep_nonempty`
  - `chargedFockSpaceSplitCARCurrentWitness`,
    `chargedFockSpaceSplitCARCurrentSugawaraMorphism`
  - `chargedFockSpace_current_constructive_J_trunc_comm`,
    `chargedFockSpace_current_exists_J_trunc_comm`,
    `chargedFockSpace_current_commutator_one_negOne`,
    `chargedFockSpace_current_commutator_zero_of_add_ne_zero`,
    `chargedFockSpace_current_commutator_central_of_add_eq_zero`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.BosonizationConstructiveCurrent`
  - `InfoGeometry.Canonical.CurrentSugawaraBridge`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical.SplitCARCurrentSource

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge

set_option synthInstance.maxHeartbeats 200000

/-- Pairing of a raw CAR mode completion `RawCARModeCompletion A` with a
Heisenberg current representation `CurrentHeisenbergRep 𝕜 V`. -/
def SplitCARCurrentWitness
    (𝕜 A V : Type*) [Field 𝕜] [CharZero 𝕜]
    [Ring A] [AddCommGroup V] [Module 𝕜 V] : Type _ :=
  RawCARModeCompletion A × CurrentHeisenbergRep 𝕜 V

namespace SplitCARCurrentWitness

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- Underlying raw CAR mode completion. -/
def source (W : SplitCARCurrentWitness 𝕜 A V) : RawCARModeCompletion A :=
  W.1

/-- Current mode family on `V`. -/
def J (W : SplitCARCurrentWitness 𝕜 A V) : Int → V →ₗ[𝕜] V :=
  W.2.J

/-- Eventual positive-mode truncation on `V`. -/
theorem trunc (W : SplitCARCurrentWitness 𝕜 A V) :
    ∀ v, ∀ᶠ l : Int in atTop, W.J l v = 0 := by
  intro v
  exact W.2.trunc v

/-- Heisenberg mode commutator identity on `V`. -/
theorem comm (W : SplitCARCurrentWitness 𝕜 A V) :
    ∀ m n, (W.J m).commutator (W.J n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0 := by
  intro m n
  exact W.2.comm m n

/-- Underlying `CurrentHeisenbergRep 𝕜 V`. -/
def toCurrentHeisenbergRep
    (W : SplitCARCurrentWitness 𝕜 A V) :
    CurrentHeisenbergRep 𝕜 V :=
  W.2

/-- Nonemptiness of `CurrentHeisenbergRep 𝕜 V` from any `SplitCARCurrentWitness`. -/
theorem toCurrentHeisenbergRep_nonempty
    (W : SplitCARCurrentWitness 𝕜 A V) :
    Nonempty (CurrentHeisenbergRep 𝕜 V) := by
  exact ⟨by unfold toCurrentHeisenbergRep; exact W.2⟩

end SplitCARCurrentWitness

/-- Concrete `SplitCARCurrentWitness` on `ChargedFockSpace 𝕜 α` paired with the
canonical exterior-Fock CAR completion. -/
noncomputable def chargedFockSpaceSplitCARCurrentWitness
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  (exteriorFockRawCAR
      (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜)
      (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis 𝕜),
    chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- The current mode family of `chargedFockSpaceSplitCARCurrentWitness` agrees with
`(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J`. -/
@[simp] theorem chargedFockSpaceSplitCARCurrentWitness_J
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  unfold chargedFockSpaceSplitCARCurrentWitness SplitCARCurrentWitness.J
  rfl

/-- Eventual positive-mode truncation of `chargedFockSpaceSplitCARCurrentWitness`. -/
theorem chargedFockSpaceSplitCARCurrentWitness_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (v : VirasoroProject.ChargedFockSpace 𝕜 α) :
    ∀ᶠ l : Int in atTop,
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J l v = 0 := by
  dsimp; simpa only [chargedFockSpaceSplitCARCurrentWitness_J] using
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc v

/-- Heisenberg commutator identity of `chargedFockSpaceSplitCARCurrentWitness`. -/
theorem chargedFockSpaceSplitCARCurrentWitness_comm
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J m).commutator
        ((chargedFockSpaceSplitCARCurrentWitness 𝕜 α).J n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0 := by
  dsimp; simpa only [chargedFockSpaceSplitCARCurrentWitness_J] using
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

/-- Nonemptiness of `SplitCARCurrentWitness` on `ChargedFockSpace 𝕜 α`. -/
theorem chargedFockSpaceSplitCARCurrentWitness_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (SplitCARCurrentWitness 𝕜
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := 𝕜) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  have h := chargedFockSpaceSplitCARCurrentWitness 𝕜 α
  exact ⟨h⟩

/-- Sugawara morphism induced by `chargedFockSpaceSplitCARCurrentWitness`. -/
noncomputable def chargedFockSpaceSplitCARCurrentSugawaraMorphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentSugawaraMorphism.ofHeisenberg
    (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep

/-- The Heisenberg component of `chargedFockSpaceSplitCARCurrentSugawaraMorphism`. -/
@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_heisenberg
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).heisenberg =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep := by
  unfold chargedFockSpaceSplitCARCurrentSugawaraMorphism
  exact CurrentSugawaraMorphism.ofHeisenberg_heisenberg _

/-- The Virasoro component of `chargedFockSpaceSplitCARCurrentSugawaraMorphism`. -/
@[simp] theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_virasoro
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α).virasoro =
      (chargedFockSpaceSplitCARCurrentWitness 𝕜 α).toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  unfold chargedFockSpaceSplitCARCurrentSugawaraMorphism
  exact CurrentSugawaraMorphism.ofHeisenberg_virasoro _

/-- Nonemptiness of `CurrentSugawaraMorphism` on `ChargedFockSpace 𝕜 α`. -/
theorem chargedFockSpaceSplitCARCurrentSugawaraMorphism_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  have h := chargedFockSpaceSplitCARCurrentSugawaraMorphism 𝕜 α
  exact ⟨h⟩

/-- Joint truncation and Heisenberg commutator law for the explicit charged-Fock
current family. -/
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
  constructor
  · exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  · exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

/-- Existence of a current family on `ChargedFockSpace 𝕜 α` satisfying eventual
truncation and the Heisenberg commutator law. -/
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
  constructor
  · exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  · exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

/-- Fundamental mode pair commutator $[J_1, J_{-1}] = 1 \cdot \mathrm{id}$ on
`ChargedFockSpace 𝕜 α`. -/
theorem chargedFockSpace_current_commutator_one_negOne
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J 1).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (-1))
      =
    (1 : 𝕜) • 1 := by
  dsimp; simpa using (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm 1 (-1)

/-- Off-diagonal current modes commute when $m + n \neq 0$. -/
theorem chargedFockSpace_current_commutator_zero_of_add_ne_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int)
    (h : m + n ≠ 0) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n)
      =
      0 := by
  dsimp; simpa [h] using (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

/-- Opposite current modes satisfy $[J_m, J_n] = m \cdot \mathrm{id}$ when $m + n = 0$. -/
theorem chargedFockSpace_current_commutator_central_of_add_eq_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m n : Int)
    (h : m + n = 0) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n)
      =
      (m : 𝕜) • 1 := by
  dsimp; simpa [h] using (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

end InfoGeometry.Canonical.SplitCARCurrentSource
