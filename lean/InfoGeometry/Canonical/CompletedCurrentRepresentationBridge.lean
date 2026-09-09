import Mathlib.Tactic
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

/-! Charged-Fock representation of the genuine locally-finite completed-current
carrier.  This owner does not invent the absent upstream affine colimit API. -/

noncomputable section
namespace InfoGeometry.Canonical.CompletedCurrentRepresentationBridge

open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open VirasoroProject

theorem completedCurrent_injective :
    Function.Injective completedCurrent := by
  intro m n hmn
  have hcoeff := congrArg
    (fun X : LocallyFiniteIntegerMatrix => X.coeff 0 m) hmn
  by_contra hne
  simp [completedCurrent_coeff, hne] at hcoeff

def CompletedCurrentModeCarrier : Type := Set.range completedCurrent

noncomputable def completedCurrentModeEquiv :
    ℤ ≃ CompletedCurrentModeCarrier :=
  Equiv.ofInjective completedCurrent completedCurrent_injective

noncomputable def completedCurrentPoint (n : ℤ) : CompletedCurrentModeCarrier :=
  completedCurrentModeEquiv n

@[simp] theorem completedCurrentModeEquiv_symm_apply_point (n : ℤ) :
    completedCurrentModeEquiv.symm (completedCurrentPoint n) = n := by
  simp [completedCurrentPoint]

@[simp] theorem completedCurrentPoint_val (n : ℤ) :
    (completedCurrentPoint n).1 = completedCurrent n := rfl

noncomputable def completedCurrentHeisenbergReadout
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X : CompletedCurrentModeCarrier) :
    VirasoroProject.HeisenbergAlgebra 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.jgen 𝕜 (completedCurrentModeEquiv.symm X)

noncomputable def completedCurrentColimitReadout
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X : CompletedCurrentModeCarrier) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) :=
  heisenbergColimitMode (𝕜 := 𝕜) (completedCurrentModeEquiv.symm X)

theorem completedCurrent_colimit_eq_heisenberg
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X : CompletedCurrentModeCarrier) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (completedCurrentColimitReadout (𝕜 := 𝕜) X) =
      completedCurrentHeisenbergReadout (𝕜 := 𝕜) X := by
  exact heisenbergFiniteModeColimitEquiv_mode
    (𝕜 := 𝕜) (completedCurrentModeEquiv.symm X)

@[simp] theorem completedCurrentHeisenbergReadout_point
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (n : ℤ) :
    completedCurrentHeisenbergReadout (𝕜 := 𝕜) (completedCurrentPoint n) =
      VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n := by
  simp [completedCurrentHeisenbergReadout]

section ChargedFock
variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable (α : 𝕜)

/-! The associative target has a genuine Mathlib Lie-algebra representation.
The completed-current range is only a mode carrier, so the representation is
defined on the canonical Heisenberg algebra and then evaluated on its
`jgen` readout. -/
noncomputable def completedCurrentHeisenbergLieRepresentation :
    LieAlgebra.Representation 𝕜 𝕜
      (VirasoroProject.HeisenbergAlgebra 𝕜)
      (ModuleOfModuleAlgebra 𝕜
        (UniversalEnvelopingAlgebra 𝕜
          (VirasoroProject.HeisenbergAlgebra 𝕜))
        (VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  UniversalEnvelopingAlgebra.representation
    (𝕜 := 𝕜)
    (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
    (V := VirasoroProject.ChargedFockSpace 𝕜 α)

theorem completedCurrentHeisenbergLieRepresentation_map_lie
    (X Y : VirasoroProject.HeisenbergAlgebra 𝕜) :
    completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α ⁅X, Y⁆ =
      ⁅completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α X,
        completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α Y⁆ := by
  exact (completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α).map_lie X Y

theorem completedCurrentHeisenbergLieRepresentation_jgen
    (n : ℤ) :
    completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α
        (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  rfl

theorem completedCurrentHeisenbergLieRepresentation_jgen_bracket
    (m n : ℤ) :
    completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α
        ⁅VirasoroProject.HeisenbergAlgebra.jgen 𝕜 m,
          VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n⁆ =
      (completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α
          (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 m)).commutator
        (completedCurrentHeisenbergLieRepresentation (𝕜 := 𝕜) α
          (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n)) := by
  exact (completedCurrentHeisenbergLieRepresentation_map_lie (𝕜 := 𝕜) α
    (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 m)
    (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n))

abbrev FockEnd :=
  VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
    VirasoroProject.ChargedFockSpace 𝕜 α

noncomputable def representedCompletedCurrentMode
    (X : CompletedCurrentModeCarrier) : FockEnd α :=
  (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
    (completedCurrentModeEquiv.symm X)

@[simp] theorem representedCompletedCurrentMode_point (n : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  simp [representedCompletedCurrentMode]

theorem representedCompletedCurrentMode_commutator (m n : ℤ) :
    (representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n)) =
      if m + n = 0 then (m : 𝕜) • (1 : FockEnd α) else 0 := by
  rw [representedCompletedCurrentMode_point,
    representedCompletedCurrentMode_point]
  exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

theorem representedCompletedCurrentMode_eq_heisenbergRepresentation
    (X : CompletedCurrentModeCarrier) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α X =
      chargedFockSpaceHeisenbergMode 𝕜 α
        (completedCurrentModeEquiv.symm X) := by
  rfl

theorem representedCompletedCurrentMode_eq_chargedFockJ (n : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  exact representedCompletedCurrentMode_point (𝕜 := 𝕜) α n

theorem virasoro_lgen_acts_on_completedCurrent (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint m)) =
      -m • representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint (r + m)) := by
  rw [representedCompletedCurrentMode_point,
    representedCompletedCurrentMode_point]
  rw [CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
  exact sugawara_current_mode_shift
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm r m

theorem completedCurrent_representation_corridor (n r : ℤ) :
    completedCurrentModeEquiv.symm (completedCurrentPoint n) = n ∧
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n ∧
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint n)) =
      -n • representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint (r + n)) := by
  refine ⟨completedCurrentModeEquiv_symm_apply_point n,
    representedCompletedCurrentMode_eq_chargedFockJ (𝕜 := 𝕜) α n, ?_⟩
  exact virasoro_lgen_acts_on_completedCurrent (𝕜 := 𝕜) α r n

end ChargedFock
end InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
