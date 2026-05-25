import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.SplitCliffordWickDiracSea
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.External.Virasoro.FockSpaceSugawara

/-!
# InfoGeometry.Canonical.SplitCliffordSourceWickVacuum

Vacuum base-case readouts for split-source Wick current commutators.

This file stays on the current owner surfaces:

* `BosonizationConstructiveCurrent` (raw/normal-ordered finite-cutoff currents),
* `SplitCliffordWickDiracSea` (finite-cutoff Heisenberg shape).

It introduces no new algebraic structures.  The only hypothesis is the
concrete boundary-term vanishing condition on the chosen vacuum/evaluation lane.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordSourceWickVacuum

open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.SplitCliffordWickDiracSea

namespace RawCARModeCompletion

variable {A : Type*} [Ring A]
variable (C : RawCARModeCompletion A)

/--
Vacuum boundary-zero condition for the diagonal/base-case current commutator
at cutoff `N` and mode `m`.
-/
def VacuumBoundaryZeroAt (N : Nat) (m : Int) : Prop :=
  RawCARModeCompletion.cutoffBoundaryTerm C N m (-m) = 0

/--
Wick vacuum base-case commutator.

If the explicit finite-cutoff boundary term vanishes, then the diagonal
commutator is exactly the Schwinger mode term `m • K`, with `K = C.central`.
-/
theorem vacuum_commutator_base_of_boundary_zero
    (N : Nat) (m : Int) (hN : m.natAbs ≤ N)
    (hVac : VacuumBoundaryZeroAt C N m) :
    comm
        (RawCARModeCompletion.cutoffCurrent C N m)
        (RawCARModeCompletion.cutoffCurrent C N (-m))
      =
      m • C.central := by
  exact
    RawCARModeCompletion.cutoffCurrent_commutator_eq_mode_of_boundary_zero
      (C := C) N m hN hVac

/--
Positive-mode spelling of the same base-case commutator (`m > 0`).

The positivity hypothesis is carried for downstream physical readout
conventions; the algebraic identity is unchanged.
-/
theorem vacuum_commutator_base_pos_mode_of_boundary_zero
    (N : Nat) (m : Int) (_hpos : 0 < m) (hN : m.natAbs ≤ N)
    (hVac : VacuumBoundaryZeroAt C N m) :
    comm
        (RawCARModeCompletion.cutoffCurrent C N m)
        (RawCARModeCompletion.cutoffCurrent C N (-m))
      =
      m • C.central := by
  exact vacuum_commutator_base_of_boundary_zero (C := C) N m hN hVac

end RawCARModeCompletion

section ExternalLaneReadout

open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/--
External-lane packaging witness: the charged Fock current datum canonically
yields a Sugawara morphism package.
-/
theorem chargedFock_currentSugawaraMorphism_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty
      (CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  CurrentSugawaraMorphism.nonempty
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/--
External Sugawara owner readout: in the packaged morphism, the Virasoro
central generator acts as identity.
-/
theorem chargedFock_currentSugawara_central_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    let M :
      CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
      CurrentSugawaraMorphism.ofHeisenberg
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)
    M.virasoro (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  let H := chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_central H

/--
External Sugawara owner readout: in the packaged morphism, the Virasoro
`L_n` generator is the corresponding Sugawara stress mode.
-/
theorem chargedFock_currentSugawara_lgen_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    let M :
      CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
      CurrentSugawaraMorphism.ofHeisenberg
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)
    M.virasoro (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
      M.heisenberg.sugawaraStressMode n := by
  let H := chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply H n

/--
External Sugawara/Virasoro commutator readout induced from the charged Fock
Heisenberg current datum.
-/
theorem chargedFock_sugawaraStressMode_virasoroBracket
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : Int) :
    let H := chargedFockSpaceCurrentHeisenbergRep 𝕜 α
    (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
      (m - n) • H.sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              (1 :
                VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                  VirasoroProject.ChargedFockSpace 𝕜 α))
          else 0 := by
  let H := chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  simpa [H] using
    (CurrentHeisenbergRep.sugawaraStressMode_virasoroBracket H m n)

/--
External packaged-lane commutator readout:
the base Heisenberg commutator can be read directly from the `heisenberg`
field of the canonical `CurrentSugawaraMorphism`.
-/
theorem chargedFock_current_commutator_base_via_morphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m : Int) :
    let M :
      CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
      CurrentSugawaraMorphism.ofHeisenberg
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)
    (M.heisenberg.J m).commutator (M.heisenberg.J (-m)) =
      (m : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  let H := chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  have h := H.comm m (-m)
  simpa [H] using h

/--
External packaged-lane positive-mode spelling of the same base readout.
-/
theorem chargedFock_current_commutator_base_pos_via_morphism
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    (m : Int) (_hpos : 0 < m) :
    let M :
      CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
      CurrentSugawaraMorphism.ofHeisenberg
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)
    (M.heisenberg.J m).commutator (M.heisenberg.J (-m)) =
      (m : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  exact chargedFock_current_commutator_base_via_morphism 𝕜 α m

/--
Bridge theorem: the external charged-Fock base commutator is also a direct
instance of the split-source Wick law interface at the diagonal pair `(m, -m)`.
-/
theorem chargedFock_current_commutator_base_via_splitSourceWick
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
              VirasoroProject.ChargedFockSpace 𝕜 α) := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with
    ⟨J, _htrunc, hWick⟩
  refine ⟨J, hWick, ?_⟩
  exact commutator_eq_central_of_add_eq_zero (Jlift := J) hWick (hmn := by simp)

/--
External Sugawara/Fock lane vacuum readout:

for positive modes, `L_n` annihilates the vacuum.
-/
theorem chargedFock_sugawara_positive_annihilates_vacuum
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜)
    {n : Int} (hn : 0 < n) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)
      (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) = 0 := by
  simpa using
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_pos_apply_vacuum
      (𝕜 := 𝕜) α hn

/--
External Sugawara/Fock lane `L₀` vacuum readout:

the vacuum is an `L₀`-eigenvector with eigenvalue `α²/2`.
-/
theorem chargedFock_sugawara_zero_mode_on_vacuum
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)
      (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) =
      (α ^ 2 / 2) • (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) := by
  simpa using
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum
      (𝕜 := 𝕜) α

/--
External-lane highest-weight packet on charged Fock vacuum:

* `c` acts as identity,
* `L₀` eigenvalue is `α²/2`,
* `L_n` annihilates vacuum for `n>0`.
-/
theorem chargedFock_sugawara_vacuum_highest_weight_packet
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
        (VirasoroProject.ChargedFockSpace.vacuum 𝕜 α) = 0) := by
  constructor
  · simpa using
      (VirasoroProject.ChargedFockSpace.sugawaraVacuum_highestWeight (𝕜 := 𝕜) α).1
  constructor
  · exact chargedFock_sugawara_zero_mode_on_vacuum (𝕜 := 𝕜) α
  · intro n hn
    exact chargedFock_sugawara_positive_annihilates_vacuum (𝕜 := 𝕜) α hn

end ExternalLaneReadout

end InfoGeometry.Canonical.SplitCliffordSourceWickVacuum
