import Mathlib.Tactic
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

/-!
# Constructive exterior current to Heisenberg-colimit bridge

The constructive bosonization owner produces completed current modes from the
literal exterior-Fock CAR construction and proves their Heisenberg central
bracket coefficient. Separately, the categorical owner realizes every
abstract Heisenberg mode `J_m` by a canonical singleton finite-stage
representative in the filtered `ModuleCat` colimit.

This file closes the exact common edge. It does not identify the completed
current coefficient carrier with the Heisenberg algebra as a whole: the former
has no repository-owned additive/Lie structure. Instead it transports the
proved central bracket output into the native Heisenberg central line and
shows that this is exactly the Lie bracket of the corresponding colimit modes.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge

open VirasoroProject
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Read only the central coefficient of a constructive completed-current
class into the genuine central line of the native Heisenberg algebra. -/
noncomputable def completedCurrentCentralReadout
    (X : CompletedCurrentCentralClass) : HeisenbergAlgebra 𝕜 :=
  (X.centralCoeff : 𝕜) • HeisenbergAlgebra.kgen 𝕜

@[simp] theorem completedCurrentCentralReadout_centralCurrentClass
    (k : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (centralCurrentClass k) =
      (k : 𝕜) • HeisenbergAlgebra.kgen 𝕜 := by
  rfl

/-- The constructive completed-current bracket reads exactly as the native
Heisenberg Lie bracket of the corresponding current generators. -/
theorem completedCurrentBracket_readout_eq_heisenbergBracket
    (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜)
        (completedCurrentModeBracket m n) =
      ⁅HeisenbergAlgebra.jgen 𝕜 m, HeisenbergAlgebra.jgen 𝕜 n⁆ := by
  rw [completedCurrentCentralReadout,
    completedCurrentModeBracket_centralCoeff_eq_heisenberg,
    HeisenbergAlgebra.lie_jgen]
  by_cases hmn : m + n = 0 <;> simp [hmn]

/-- The same bracket equality expressed entirely through canonical finite-stage
representatives in the filtered Heisenberg colimit. -/
theorem completedCurrentBracket_readout_eq_colimitBracket
    (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜)
        (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) n)⁆ := by
  rw [heisenbergFiniteModeColimitEquiv_mode,
    heisenbergFiniteModeColimitEquiv_mode]
  exact completedCurrentBracket_readout_eq_heisenbergBracket (𝕜 := 𝕜) m n

/-- The repository-owned literal exterior-Fock CAR packet on the integer mode
space. This is a transparent compatibility name, not a second source carrier. -/
abbrev canonicalExteriorFockRawCAR :=
  directSumExteriorFockRawCAR 𝕜

/-- The completed-current Heisenberg law is obtained from the literal
exterior-Fock wedge/contraction CAR packet, not supplied as an assumption. -/
theorem canonicalExteriorFock_completedCurrent_heisenberg
    (m n : ℤ) :
    CCRBracketCompleted
        (canonicalExteriorFockRawCAR (𝕜 := 𝕜))
        (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m)
        (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) n) =
      if m + n = 0 then
        m •
          (1 : InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
            (R := 𝕜)
            (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      else 0 := by
  exact directSumExteriorFock_constructiveHeisenbergCurrent 𝕜 m n

/-- Full coefficientwise completion packet for the canonical exterior-Fock
source. Finite cutoff diagonals stabilize to the completed modes, the
noncentral remainder cancels, and the crossing coefficient is the Heisenberg
coefficient. -/
theorem canonicalExteriorFock_completion_packet
    (m n : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j) ∧
    (∀ i j : ℤ, formalCurrentNoncentralCoeff m n i j = 0) ∧
    (formalCurrentCentralCoeff m n = if m + n = 0 then m else 0) ∧
    CCRBracketCompleted
        (canonicalExteriorFockRawCAR (𝕜 := 𝕜))
        (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m)
        (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) n) =
      if m + n = 0 then
        m • (canonicalExteriorFockRawCAR (𝕜 := 𝕜)).central
      else 0 := by
  exact constructiveHeisenbergCurrent_from_completedCurrent
    (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m n

/-- Source-to-colimit compatibility packet. The source current law and its
coefficientwise completion are constructive, while the bracket readout is the
native categorical Heisenberg bracket. -/
theorem exteriorFock_to_heisenbergColimit_packet
    (m n : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j) ∧
    (completedCurrentCentralReadout (𝕜 := 𝕜)
        (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) n)⁆) := by
  rcases canonicalExteriorFock_completion_packet (𝕜 := 𝕜) m n with
    ⟨hm, hn, _hnoncentral, _hcentral, _hcurrent⟩
  exact ⟨hm, hn,
    completedCurrentBracket_readout_eq_colimitBracket (𝕜 := 𝕜) m n⟩

/-- After the source current has reached the colimit Heisenberg mode system,
the repository-owned Sugawara representation shifts its represented current
modes by `[L_r,J_m] = -m J_(r+m)`. -/
theorem exteriorFock_colimit_virasoro_shift
    (α : 𝕜) (r m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        -m • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (r + m) := by
  exact virasoro_lgen_colimit_mode_shift (𝕜 := 𝕜) α r m

/-- Compact corridor theorem from coefficientwise exterior-Fock completion,
through the categorical Heisenberg bracket, to the represented Virasoro mode
shift. -/
theorem constructive_exterior_heisenberg_virasoro_corridor
    (α : 𝕜) (m n r : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    completedCurrentCentralReadout (𝕜 := 𝕜)
        (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) n)⁆ ∧
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        -m • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (r + m) := by
  rcases exteriorFock_to_heisenbergColimit_packet (𝕜 := 𝕜) m n with
    ⟨hm, _hn, hbracket⟩
  exact ⟨hm, hbracket,
    exteriorFock_colimit_virasoro_shift (𝕜 := 𝕜) α r m⟩

end InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
