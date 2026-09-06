import InfoGeometry.Canonical.SplitCliffordSourceWickVacuum
import InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

/-!
# InfoGeometry.Canonical.SplitCliffordVacuumSugawaraBridge

Concrete bridge from split-Clifford Wick base-case data to the external
Heisenberg/Sugawara owner APIs.

This file introduces no new algebraic structure.  It only repackages already
proved interfaces and readouts.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordVacuumSugawaraBridge

open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.SplitCliffordSourceWickVacuum
open Filter

/--
Given explicit truncation and Wick commutator laws, the source current family
closes to the external `CurrentHeisenbergRep`.
-/
def vacuum_closes_external_heisenberg_rep
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (J : Int → V →ₗ[𝕜] V)
    (h_trunc : ∀ v : V, ∀ᶠ l : Int in atTop, J l v = 0)
    (h_wick : SplitSourceEndWickLaw J) :
    CurrentHeisenbergRep 𝕜 V := by
  let W : SplitCliffordHeisenbergWitness 𝕜 V :=
    { J := J, trunc := h_trunc, comm := h_wick }
  exact splitClifford_to_currentHeisenbergRep W

/--
The same data also closes to the packaged external Sugawara morphism surface.
-/
noncomputable def vacuum_closes_external_sugawara_morphism
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (J : Int → V →ₗ[𝕜] V)
    (h_trunc : ∀ v : V, ∀ᶠ l : Int in atTop, J l v = 0)
    (h_wick : SplitSourceEndWickLaw J) :
    CurrentSugawaraMorphism 𝕜 V := by
  let W : SplitCliffordHeisenbergWitness 𝕜 V :=
    { J := J, trunc := h_trunc, comm := h_wick }
  exact splitClifford_to_currentSugawaraMorphism W

/-- Explicit Wick data read out as the exact external Heisenberg current laws. -/
theorem vacuum_closes_external_heisenberg_rep_readout
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (J : Int → V →ₗ[𝕜] V)
    (h_trunc : ∀ v : V, ∀ᶠ l : Int in atTop, J l v = 0)
    (h_wick : SplitSourceEndWickLaw J) :
    (vacuum_closes_external_heisenberg_rep J h_trunc h_wick).J = J
      ∧ (vacuum_closes_external_heisenberg_rep J h_trunc h_wick).trunc = h_trunc
      ∧ ∀ m n,
          ((vacuum_closes_external_heisenberg_rep J h_trunc h_wick).J m).commutator
              ((vacuum_closes_external_heisenberg_rep J h_trunc h_wick).J n) =
            if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0 := by
  exact ⟨rfl, rfl, (vacuum_closes_external_heisenberg_rep J h_trunc h_wick).comm⟩

/--
External charged-Fock base commutator readout in bridge form:
`[J_m, J_{-m}] = m • 1`.
-/
theorem chargedFock_external_current_commutator_base
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m : Int) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      SplitSourceEndWickLaw J ∧
      (J m).commutator (J (-m)) =
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α) :=
  chargedFock_current_commutator_base_via_splitSourceWick (𝕜 := 𝕜) α m

/--
External Sugawara `L₀` vacuum eigenvalue readout:
`L₀ |0⟩ = (α²/2) |0⟩`.
-/
theorem chargedFock_external_sugawara_zero_mode_on_vacuum
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
      (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) =
      (α ^ 2 / 2) • (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) :=
  chargedFock_sugawara_zero_mode_on_vacuum (𝕜 := 𝕜) α

/--
External charged-Fock highest-weight packet readout through the bridge.
-/
theorem chargedFock_external_sugawara_vacuum_highest_weight_packet
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
      (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
      (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
        = VirasoroProject.ChargedFockSpace.vacuum 𝕜 α
      ∧
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
      (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
        = (α ^ 2 / 2) • (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α)
      ∧
    (∀ n : Int, 0 < n →
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
        (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) = 0) :=
  chargedFock_sugawara_vacuum_highest_weight_packet (𝕜 := 𝕜) α

end InfoGeometry.Canonical.SplitCliffordVacuumSugawaraBridge
