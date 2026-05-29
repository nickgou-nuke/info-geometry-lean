import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom

/-!
# Tensor modular atom current source

This file does not invent a new current algebra. It reuses the owned charged
Fock Heisenberg current and packages it under the split-Clifford bridge.

The finite `Cl(1,1)` atom is kept separate from the mode current:

* the finite local seed lives in `TomitaKreinNilpotentAtom`;
* the Wick-corrected current law lives in `BosonizationConstructiveCurrent`;
* the `CurrentHeisenbergRep` and Sugawara bridge live in
  `CurrentSugawaraBridge`;
* this file only packages those owner theorems into the requested source-side
  witness surface.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorModularAtomCurrent

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open VirasoroProject

section WickMechanism

variable {A : Type*} [Ring A]

/--
The source-side Wick contraction law is the owner theorem from the
constructive current layer.
-/
theorem wickContraction_current
    (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 := by
  simpa using normalOrderedCurrent_heisenberg_from_matrixUnit C m n

/--
The finite-cutoff boundary form of the same calculation.

This is the explicit reindexed cutoff boundary plus the window-crossing
correction.
-/
theorem wickContraction_cutoffBoundary
    (C : RawCARModeCompletion A) (N : Nat) (m n : Int) :
    comm (RawCARModeCompletion.cutoffCurrent C N m)
        (RawCARModeCompletion.cutoffCurrent C N n) =
      RawCARModeCompletion.cutoffBoundaryTerm C N m n +
        RawCARModeCompletion.cutoffWindowCrossingTerm C N m n := by
  simpa using
    RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_windowCrossing C N m n

end WickMechanism

section ChargedFockWitness

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
variable (α : 𝕜)

/--
The concrete tensor-modular atom witness is the existing charged-Fock
Heisenberg current packaged as a split-Clifford witness.

This is the exact current-side data required by the bridge:
current modes, local truncation, and the Heisenberg commutator.
-/
noncomputable def tensorModularAtomHeisenbergWitness :
    SplitCliffordHeisenbergWitness 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) where
  J := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
  trunc := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
  comm := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm

@[simp] theorem tensorModularAtomHeisenbergWitness_J (n : Int) :
    (tensorModularAtomHeisenbergWitness 𝕜 α).J n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n :=
  rfl

@[simp] theorem tensorModularAtomHeisenbergWitness_trunc :
    (tensorModularAtomHeisenbergWitness 𝕜 α).trunc =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc :=
  rfl

@[simp] theorem tensorModularAtomHeisenbergWitness_comm :
    (tensorModularAtomHeisenbergWitness 𝕜 α).comm =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm :=
  rfl

/-- The tensor modular atom witness yields the exact current interface. -/
noncomputable def tensorModularAtom_toCurrentHeisenbergRep :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  splitClifford_to_currentHeisenbergRep (tensorModularAtomHeisenbergWitness 𝕜 α)

/-- The tensor modular atom witness yields the packaged Sugawara morphism. -/
noncomputable def tensorModularAtom_toCurrentSugawaraMorphism :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  splitClifford_to_currentSugawaraMorphism (tensorModularAtomHeisenbergWitness 𝕜 α)

/--
Bundled bridge export via owner theorem route: packaged Sugawara morphism together
with exact current representation on the tensor modular-atom carrier.
-/
noncomputable def tensorModularAtom_toCurrentSugawaraMorphism_and_current :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) ×
      CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  splitClifford_currentSugawara_and_current (tensorModularAtomHeisenbergWitness 𝕜 α)

/-- The tensor modular atom witness yields the downstream Sugawara representation. -/
noncomputable def tensorModularAtom_to_sugawaraRepresentation :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
      (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) :=
  (tensorModularAtomHeisenbergWitness 𝕜 α).currentSugawaraRepresentation

/--
Bundled bridge export via owner theorem route: exact current representation
plus downstream Sugawara representation on the tensor modular-atom carrier.
-/
noncomputable def tensorModularAtom_toCurrentAndSugawara
    :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) ×
      (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
        (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  splitClifford_current_and_sugawara (tensorModularAtomHeisenbergWitness 𝕜 α)

/--
The exact source-side bridge: the charged-Fock current witness is already a
split-Clifford witness, so the current and Sugawara packages are immediate.
-/
noncomputable def tensorModularAtom_current_and_sugawara
    :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) ×
      (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
        (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  tensorModularAtom_toCurrentAndSugawara (𝕜 := 𝕜) (α := α)

/--
Companion bridge surface exposing the packaged Sugawara morphism together with
its current witness on the tensor modular-atom carrier.
-/
noncomputable def tensorModularAtom_currentSugawara_and_current
    :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) ×
      CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  tensorModularAtom_toCurrentSugawaraMorphism_and_current (𝕜 := 𝕜) (α := α)

end ChargedFockWitness

end InfoGeometry.Canonical.TensorModularAtomCurrent
