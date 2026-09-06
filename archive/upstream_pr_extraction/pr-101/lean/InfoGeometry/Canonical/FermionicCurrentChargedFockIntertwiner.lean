import Mathlib.Tactic
import InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

/-!
# Fermionic current to charged-Fock current intertwiner

This owner closes the theorem-honest current-level bosonization edge that is
already available from the repository's native ingredients.

The source is the literal exterior-Fock CAR representation from
`CanonicalNormalOrdering`.  Its finite normal-ordered current is the genuine
endomorphism

`J_m^(N) = sum_{a in [-N,N]} :psiPlus_a psiMinus_{-(a+m)}:`.

The constructive completion owner separately proves coefficientwise
stabilization of the corresponding locally-finite diagonal current to
`completedCurrent m`.  `CompletedCurrentRepresentationBridge` then represents
that actual completed-current object by exactly the repository-owned charged
Fock Heisenberg operator `J_m`.

Thus this file proves the concrete current corridor

finite exterior-Fock current
  -> completed locally-finite current object
  -> Heisenberg colimit mode
  -> charged-Fock `J_m`
  -> Sugawara/Virasoro action.

It does not assert an isomorphism of the fermionic and bosonic state spaces.
That stronger boson--fermion correspondence requires one additional theorem:
pointwise stabilization of the finite exterior-Fock cutoff-current
endomorphisms to a genuine Heisenberg action on the infinite exterior-Fock
module, followed by the Heisenberg Verma universal property.
-/

noncomputable section

namespace InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner

open Filter
open VirasoroProject
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CanonicalNormalOrdering
open InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
open InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The literal infinite-mode exterior-Fock carrier used by the constructive
CAR current owner. -/
abbrev FermionicFock : Type _ :=
  Fock (R := 𝕜) (M := IntModeSpace 𝕜)

/-- Endomorphism algebra of the literal exterior-Fock carrier. -/
abbrev FermionicEnd : Type _ :=
  EndFock (R := 𝕜) (M := IntModeSpace 𝕜)

/-- Canonical exterior-Fock raw CAR packet.  This is the literal
wedge/contraction representation, not an adapter assumption. -/
abbrev fermionicRawCAR : RawCARModeCompletion (FermionicEnd (𝕜 := 𝕜)) :=
  canonicalExteriorFockRawCAR (𝕜 := 𝕜)

/-- Genuine finite normal-ordered fermionic current endomorphism. -/
def fermionicCutoffCurrent (N : ℕ) (m : ℤ) : FermionicEnd (𝕜 := 𝕜) :=
  (fermionicRawCAR (𝕜 := 𝕜)).cutoffCurrent N m

/-- The cutoff current is exactly the finite sum of literal normal-ordered
matrix units in exterior Fock space. -/
theorem fermionicCutoffCurrent_eq_sum (N : ℕ) (m : ℤ) :
    fermionicCutoffCurrent (𝕜 := 𝕜) N m =
      ∑ a ∈ integerWindow N,
        (fermionicRawCAR (𝕜 := 𝕜)).matrixUnit a (a + m) := by
  rfl

/-- The actual locally-finite completed-current object attached to the
fermionic current mode `m`. -/
noncomputable def fermionicCompletedCurrent (m : ℤ) : CompletedCurrentModeCarrier :=
  completedCurrentPoint m

@[simp] theorem fermionicCompletedCurrent_val (m : ℤ) :
    (fermionicCompletedCurrent m).1 = completedCurrent m := by
  simp [fermionicCompletedCurrent]

/-- Coefficientwise stabilization of the finite diagonal-current matrices to
the actual completed-current object associated with mode `m`. -/
theorem fermionicCurrent_coefficientwise_completion (m : ℤ) :
    ∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j =
        (fermionicCompletedCurrent m).1.coeff i j := by
  intro i j
  rcases (canonicalExteriorFock_completion_packet (𝕜 := 𝕜) m 0).1 i j with
    ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  simpa [fermionicCompletedCurrent] using hN0 N hN

/-- The completed fermionic current reads out as the canonical Heisenberg
colimit mode. -/
@[simp] theorem fermionicCompletedCurrent_colimit_readout (m : ℤ) :
    completedCurrentColimitReadout (𝕜 := 𝕜) (fermionicCompletedCurrent m) =
      heisenbergColimitMode (𝕜 := 𝕜) m := by
  simp [fermionicCompletedCurrent]

/-- The Heisenberg algebra readout of the completed fermionic current is the
native generator `J_m`. -/
@[simp] theorem fermionicCompletedCurrent_heisenberg_readout (m : ℤ) :
    completedCurrentHeisenbergReadout (𝕜 := 𝕜) (fermionicCompletedCurrent m) =
      HeisenbergAlgebra.jgen 𝕜 m := by
  simp [fermionicCompletedCurrent]

section ChargedFock

variable (α : 𝕜)

abbrev BosonicFock : Type* := ChargedFockSpace 𝕜 α
abbrev BosonicEnd : Type* :=
  BosonicFock (𝕜 := 𝕜) α →ₗ[𝕜] BosonicFock (𝕜 := 𝕜) α

/-- Current-level bosonization map on the genuine completed-current carrier.
This is source-faithful because its argument is the actual locally-finite
completed current object, not an integer label or an assumed adapter. -/
noncomputable def fermionToBosonCurrent
    (X : CompletedCurrentModeCarrier) : BosonicEnd (𝕜 := 𝕜) α :=
  representedCompletedCurrentMode (𝕜 := 𝕜) α X

/-- On the completed current produced from the literal exterior-Fock source,
the current-level bosonization map is exactly the charged-Fock Heisenberg
operator `J_m`. -/
theorem fermionToBosonCurrent_mode (m : ℤ) :
    fermionToBosonCurrent (𝕜 := 𝕜) α (fermionicCompletedCurrent m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  simpa [fermionToBosonCurrent, fermionicCompletedCurrent] using
    representedCompletedCurrentMode_eq_chargedFockJ (𝕜 := 𝕜) α m

/-- The same target operator is the represented image of the native abstract
Heisenberg generator obtained from the completed fermionic current. -/
theorem fermionToBosonCurrent_eq_heisenbergRepresentation
    (X : CompletedCurrentModeCarrier) :
    fermionToBosonCurrent (𝕜 := 𝕜) α X =
      chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α
        (completedCurrentHeisenbergReadout (𝕜 := 𝕜) X) := by
  exact representedCompletedCurrentMode_eq_heisenbergRepresentation
    (𝕜 := 𝕜) α X

/-- The represented images of two completed fermionic currents satisfy the
exact Heisenberg commutator on charged Fock space. -/
theorem fermionToBosonCurrent_commutator (m n : ℤ) :
    (fermionToBosonCurrent (𝕜 := 𝕜) α (fermionicCompletedCurrent m)).commutator
      (fermionToBosonCurrent (𝕜 := 𝕜) α (fermionicCompletedCurrent n)) =
      if m + n = 0 then
        (m : 𝕜) • (1 : BosonicEnd (𝕜 := 𝕜) α)
      else 0 := by
  simpa [fermionToBosonCurrent, fermionicCompletedCurrent] using
    representedCompletedCurrentMode_commutator (𝕜 := 𝕜) α m n

/-- Sugawara/Virasoro acts on the represented fermionic current by the native
mode shift `[L_r,J_m] = -m J_(r+m)`. -/
theorem virasoro_acts_on_bosonizedFermionicCurrent (r m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (fermionToBosonCurrent (𝕜 := 𝕜) α (fermionicCompletedCurrent m)) =
      -m • fermionToBosonCurrent (𝕜 := 𝕜) α
        (fermionicCompletedCurrent (r + m)) := by
  simpa [fermionToBosonCurrent, fermionicCompletedCurrent] using
    virasoro_lgen_acts_on_completedCurrent (𝕜 := 𝕜) α r m

/-- Full source-faithful current corridor.  The first component is genuine
coefficientwise completion of the fermionic cutoff family; the second is the
exact charged-Fock current equality; the third is the Virasoro mode shift. -/
theorem fermionic_to_bosonic_current_intertwiner_packet
    (r m : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j =
        (fermionicCompletedCurrent m).1.coeff i j) ∧
    fermionToBosonCurrent (𝕜 := 𝕜) α (fermionicCompletedCurrent m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (fermionToBosonCurrent (𝕜 := 𝕜) α (fermionicCompletedCurrent m)) =
      -m • fermionToBosonCurrent (𝕜 := 𝕜) α
        (fermionicCompletedCurrent (r + m)) := by
  exact ⟨fermionicCurrent_coefficientwise_completion (𝕜 := 𝕜) m,
    fermionToBosonCurrent_mode (𝕜 := 𝕜) α m,
    virasoro_acts_on_bosonizedFermionicCurrent (𝕜 := 𝕜) α r m⟩

end ChargedFock

end InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner
