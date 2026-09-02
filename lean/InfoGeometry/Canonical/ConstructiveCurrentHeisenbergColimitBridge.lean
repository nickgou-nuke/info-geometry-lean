import Mathlib.Tactic
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/-! The constructive exterior-current bracket is read into the genuine
Heisenberg central line and compared with the canonical singleton-stage
representatives.  The completed-current coefficient carrier itself is not
declared to be a Lie algebra. -/
noncomputable section
namespace InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge

open VirasoroProject
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

noncomputable def completedCurrentCentralReadout
    (X : CompletedCurrentCentralClass) : HeisenbergAlgebra 𝕜 :=
  (X.centralCoeff : 𝕜) • HeisenbergAlgebra.kgen 𝕜

@[simp] theorem completedCurrentCentralReadout_centralCurrentClass (k : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (centralCurrentClass k) =
      (k : 𝕜) • HeisenbergAlgebra.kgen 𝕜 := by
  rfl

theorem completedCurrentBracket_readout_eq_heisenbergBracket (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅HeisenbergAlgebra.jgen 𝕜 m, HeisenbergAlgebra.jgen 𝕜 n⁆ := by
  rw [completedCurrentCentralReadout,
    completedCurrentModeBracket_centralCoeff_eq_heisenberg,
    HeisenbergAlgebra.lie_jgen]
  by_cases h : m + n = 0 <;> simp [h]

theorem completedCurrentBracket_readout_eq_colimitBracket (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode n)⁆ := by
  rw [heisenbergFiniteModeColimitEquiv_mode,
    heisenbergFiniteModeColimitEquiv_mode]
  exact completedCurrentBracket_readout_eq_heisenbergBracket (𝕜 := 𝕜) m n

abbrev canonicalExteriorFockRawCAR := directSumExteriorFockRawCAR 𝕜

theorem canonicalExteriorFock_completedCurrent_heisenberg (m n : ℤ) :
    CCRBracketCompleted (canonicalExteriorFockRawCAR (𝕜 := 𝕜))
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m)
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) n) =
      if m + n = 0 then m • (1 :
        InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock (R := 𝕜)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      else 0 := by
  exact directSumExteriorFock_constructiveHeisenbergCurrent 𝕜 m n

theorem exteriorFock_to_heisenbergColimit_packet (m n : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j) ∧
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode n)⁆ := by
  rcases constructiveHeisenbergCurrent_from_completedCurrent
      (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m n with ⟨hm, hn, _, _, _⟩
  exact ⟨hm, hn, completedCurrentBracket_readout_eq_colimitBracket m n⟩

/-! The represented endpoint is the existing charged-Fock current owner. -/
noncomputable def completedModeRepresentation (α : 𝕜) (n : ℤ) :=
  (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n

@[simp] theorem completedModeRepresentation_eq_current (α : 𝕜) (n : ℤ) :
    completedModeRepresentation (𝕜 := 𝕜) α n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n :=
  rfl

theorem completedModeRepresentation_bracket (α : 𝕜) (m n : ℤ) :
    (completedModeRepresentation (𝕜 := 𝕜) α m).commutator
        (completedModeRepresentation (𝕜 := 𝕜) α n) =
      if m + n = 0 then (m : 𝕜) • (1 : _) else 0 := by
  exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

theorem completedModeRepresentation_sugawara_shift
    (α : 𝕜) (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      (completedModeRepresentation (𝕜 := 𝕜) α m) =
        -m • completedModeRepresentation (𝕜 := 𝕜) α (r + m) := by
  rw [CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
  exact VirasoroProject.commutator_sugawaraGen_heiOper
    (heiOper := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J)
    (heiTrunc := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc)
    (heiComm := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm) r m

theorem completedModeRepresentation_packet (α : 𝕜) (m n : ℤ) :
    completedModeRepresentation (𝕜 := 𝕜) α m =
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    (completedModeRepresentation (𝕜 := 𝕜) α m).commutator
        (completedModeRepresentation (𝕜 := 𝕜) α n) =
      if m + n = 0 then (m : 𝕜) • (1 : _) else 0 := by
  exact ⟨completedModeRepresentation_eq_current α m,
    completedModeRepresentation_bracket α m n⟩

end InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
