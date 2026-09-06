import Mathlib.Tactic
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Completed locally-finite current representation bridge

The constructive bosonization owner already constructs, for every integer mode
`n`, a genuine locally-finite diagonal current `completedCurrent n` with
coefficient law

`(completedCurrent n).coeff i j = if j = i + n then 1 else 0`.

This file closes the remaining representation edge.  First it proves that the
locally-finite current itself determines its mode label uniquely.  The image of
`completedCurrent` is therefore canonically equivalent to `ℤ`.  We then use
that equivalence to represent the *actual completed-current object* by the
repository-owned charged-Fock Heisenberg current operator.

No linear or Lie structure is invented on `LocallyFiniteIntegerMatrix` or on
its completed-mode image.  The representation is a map of the genuine mode
carrier, and its compatibility with the Heisenberg and Virasoro owners is
proved on the canonical completed modes.
-/

noncomputable section

namespace InfoGeometry.Canonical.CompletedCurrentRepresentationBridge

open VirasoroProject
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge

/-- A completed diagonal current determines its integer displacement uniquely. -/
theorem completedCurrent_injective :
    Function.Injective completedCurrent := by
  intro m n hmn
  have hcoeff := congrArg
    (fun X : LocallyFiniteIntegerMatrix => X.coeff 0 m) hmn
  by_contra hne
  simp [completedCurrent_coeff, hne] at hcoeff

/-- The genuine carrier consisting exactly of the locally-finite completed
current modes constructed by `completedCurrent`. -/
def CompletedCurrentModeCarrier : Type :=
  Set.range completedCurrent

/-- Canonical equivalence between the integer mode label and the actual
locally-finite completed-current carrier. -/
noncomputable def completedCurrentModeEquiv :
    ℤ ≃ CompletedCurrentModeCarrier :=
  Equiv.ofInjective completedCurrent completedCurrent_injective

/-- Canonical completed-current object with mode label `n`. -/
noncomputable def completedCurrentPoint (n : ℤ) : CompletedCurrentModeCarrier :=
  completedCurrentModeEquiv n

@[simp] theorem completedCurrentModeEquiv_symm_apply_point (n : ℤ) :
    completedCurrentModeEquiv.symm (completedCurrentPoint n) = n := by
  simp [completedCurrentPoint]

@[simp] theorem completedCurrentPoint_val (n : ℤ) :
    (completedCurrentPoint n).1 = completedCurrent n := by
  rfl

/-- The abstract Heisenberg mode represented by a genuine completed-current
object.  The mode label is recovered from the locally-finite current itself. -/
noncomputable def completedCurrentHeisenbergReadout
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X : CompletedCurrentModeCarrier) : HeisenbergAlgebra 𝕜 :=
  HeisenbergAlgebra.jgen 𝕜 (completedCurrentModeEquiv.symm X)

@[simp] theorem completedCurrentHeisenbergReadout_point
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (n : ℤ) :
    completedCurrentHeisenbergReadout (𝕜 := 𝕜) (completedCurrentPoint n) =
      HeisenbergAlgebra.jgen 𝕜 n := by
  simp [completedCurrentHeisenbergReadout]

/-- The same genuine completed-current object read through the categorical
Heisenberg colimit. -/
noncomputable def completedCurrentColimitReadout
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X : CompletedCurrentModeCarrier) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) :=
  heisenbergColimitMode (𝕜 := 𝕜) (completedCurrentModeEquiv.symm X)

@[simp] theorem completedCurrentColimitReadout_point
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (n : ℤ) :
    completedCurrentColimitReadout (𝕜 := 𝕜) (completedCurrentPoint n) =
      heisenbergColimitMode (𝕜 := 𝕜) n := by
  simp [completedCurrentColimitReadout]

/-- The colimit equivalence sends the represented completed-current object to
the same native Heisenberg generator. -/
theorem completedCurrent_colimit_eq_heisenberg
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X : CompletedCurrentModeCarrier) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (completedCurrentColimitReadout (𝕜 := 𝕜) X) =
      completedCurrentHeisenbergReadout (𝕜 := 𝕜) X := by
  simp [completedCurrentColimitReadout, completedCurrentHeisenbergReadout,
    heisenbergFiniteModeColimitEquiv_mode]

section ChargedFock

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable (α : 𝕜)

abbrev Fock : Type* := ChargedFockSpace 𝕜 α
abbrev FockEnd : Type* := Fock (𝕜 := 𝕜) α →ₗ[𝕜] Fock (𝕜 := 𝕜) α

/-- Genuine represented map from the locally-finite completed-current mode
carrier to charged-Fock endomorphisms.  Its argument is the completed current
object itself; the unique mode index is recovered through
`completedCurrentModeEquiv.symm`. -/
noncomputable def representedCompletedCurrentMode
    (X : CompletedCurrentModeCarrier) : FockEnd (𝕜 := 𝕜) α :=
  (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J
    (completedCurrentModeEquiv.symm X)

/-- On the canonical locally-finite current `completedCurrent n`, the genuine
representation map is exactly the current `J_n` supplied by the categorical
`CurrentHeisenbergRep`. -/
@[simp] theorem representedCompletedCurrentMode_point (n : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n) =
      (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J n := by
  simp [representedCompletedCurrentMode]

/-- The represented completed current is also exactly the repository-owned
charged-Fock current family, not merely an operator with the same bracket. -/
theorem representedCompletedCurrentMode_eq_chargedFockJ (n : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rw [representedCompletedCurrentMode_point]
  change colimitCurrentMode (𝕜 := 𝕜) α n =
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n
  exact colimitCurrentMode_eq_chargedFock (𝕜 := 𝕜) α n

/-- The charged-Fock representation of the Heisenberg readout of a completed
current equals the direct represented-current map for every completed-current
object in the genuine image carrier. -/
theorem representedCompletedCurrentMode_eq_heisenbergRepresentation
    (X : CompletedCurrentModeCarrier) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α X =
      chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α
        (completedCurrentHeisenbergReadout (𝕜 := 𝕜) X) := by
  let n := completedCurrentModeEquiv.symm X
  change (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J n =
    chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α
      (HeisenbergAlgebra.jgen 𝕜 n)
  rw [show (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J n =
      colimitCurrentMode (𝕜 := 𝕜) α n by rfl]
  rw [colimitCurrentMode_eq_chargedFock]
  rfl

/-- The genuine represented completed-current modes satisfy the native
Heisenberg commutator law because they are exactly the `CurrentHeisenbergRep`
mode family. -/
theorem representedCompletedCurrentMode_commutator (m n : ℤ) :
    (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint m)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint n)) =
      if m + n = 0 then
        (m : 𝕜) • (1 : FockEnd (𝕜 := 𝕜) α)
      else 0 := by
  rw [representedCompletedCurrentMode_point,
    representedCompletedCurrentMode_point]
  exact (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).comm m n

/-- Actual represented Virasoro action on a genuine locally-finite completed
current mode. -/
theorem virasoro_lgen_acts_on_completedCurrent
    (r m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint m)) =
      -m • representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint (r + m)) := by
  rw [representedCompletedCurrentMode_point,
    representedCompletedCurrentMode_point]
  exact virasoro_lgen_colimit_mode_shift (𝕜 := 𝕜) α r m

/-- Final object-level corridor: the actual locally-finite completed current,
its colimit representative, its abstract Heisenberg mode, and its charged-Fock
operator are all compatible, and Virasoro shifts the represented object to the
represented completed current with label `r+m`. -/
theorem completedCurrent_representation_corridor
    (r m : ℤ) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (completedCurrentColimitReadout (𝕜 := 𝕜) (completedCurrentPoint m)) =
      HeisenbergAlgebra.jgen 𝕜 m ∧
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint m)) =
      -m • representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint (r + m)) := by
  exact ⟨by simp [completedCurrentColimitReadout],
    representedCompletedCurrentMode_eq_chargedFockJ (𝕜 := 𝕜) α m,
    virasoro_lgen_acts_on_completedCurrent (𝕜 := 𝕜) α r m⟩

end ChargedFock

end InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
