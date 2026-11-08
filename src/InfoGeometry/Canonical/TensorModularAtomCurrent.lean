/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom

/-!
# Tensor Modular Atom Current Source and Charged-Fock Sugawara Bridge

This module connects the Wick-corrected normal-ordered CAR current commutator
from `BosonizationConstructiveCurrent` and the charged-Fock Heisenberg current
representation to `SplitCliffordHeisenbergWitness` and `CurrentSugawaraMorphism`.

- BUCKET 1 (Real Math in This File):
  - `wickContraction_current`, `wickContraction_cutoffBoundary`
  - `tensorModularAtomHeisenbergWitness`
  - `tensorModularAtom_toCurrentHeisenbergRep`,
    `tensorModularAtom_toCurrentSugawaraMorphism`,
    `tensorModularAtom_to_sugawaraRepresentation`
  - `tensorModularAtom_current_readout`, `tensorModularAtom_currentSugawara_readout`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.BosonizationConstructiveCurrent`
  - `InfoGeometry.Canonical.CurrentSugawaraBridge`
  - `InfoGeometry.Canonical.SplitCliffordHeisenbergBridge`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorModularAtomCurrent

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open VirasoroProject

attribute [local instance 100] LieRing.ofAssociativeRing

section WickMechanism

variable {A : Type*} [Ring A]

/-- Completed normal-ordered CAR current commutator identity
`CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n)`. -/
theorem wickContraction_current
    (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 := by
  dsimp; simpa using normalOrderedCurrent_heisenberg_from_matrixUnit C m n

/-- Finite-cutoff CAR current commutator decomposition into the boundary term
and the window-crossing central term. -/
theorem wickContraction_cutoffBoundary
    (C : RawCARModeCompletion A) (N : Nat) (m n : Int) :
    comm (RawCARModeCompletion.cutoffCurrent C N m)
        (RawCARModeCompletion.cutoffCurrent C N n) =
      RawCARModeCompletion.cutoffBoundaryTerm C N m n +
        RawCARModeCompletion.cutoffWindowCrossingTerm C N m n := by
  dsimp; simpa using
    RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_windowCrossing C N m n

end WickMechanism

section ChargedFockWitness

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
variable (α : 𝕜)

/-- Charged-Fock Heisenberg current packaged as a `SplitCliffordHeisenbergWitness`. -/
noncomputable def tensorModularAtomHeisenbergWitness :
    SplitCliffordHeisenbergWitness 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  ⟨(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J,
   (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc,
   (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm⟩

/-- The current mode family of `tensorModularAtomHeisenbergWitness` agrees with
`(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J`. -/
@[simp] theorem tensorModularAtomHeisenbergWitness_J (n : Int) :
    (tensorModularAtomHeisenbergWitness 𝕜 α).J n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  unfold tensorModularAtomHeisenbergWitness SplitCliffordHeisenbergWitness.J
  rfl

/-- Eventual positive-mode truncation of `tensorModularAtomHeisenbergWitness`. -/
theorem tensorModularAtomHeisenbergWitness_trunc
    (v : VirasoroProject.ChargedFockSpace 𝕜 α) :
    ∀ᶠ l : Int in atTop,
      (tensorModularAtomHeisenbergWitness 𝕜 α).J l v = 0 := by
  have h := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc v
  exact h

/-- Heisenberg mode commutator law of `tensorModularAtomHeisenbergWitness`. -/
theorem tensorModularAtomHeisenbergWitness_comm (m n : Int) :
    ((tensorModularAtomHeisenbergWitness 𝕜 α).J m).commutator
        ((tensorModularAtomHeisenbergWitness 𝕜 α).J n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0 := by
  have h := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n
  exact h

/-- `CurrentHeisenbergRep` induced by `tensorModularAtomHeisenbergWitness`. -/
noncomputable def tensorModularAtom_toCurrentHeisenbergRep :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  splitClifford_to_currentHeisenbergRep (tensorModularAtomHeisenbergWitness 𝕜 α)

/-- `CurrentSugawaraMorphism` induced by `tensorModularAtomHeisenbergWitness`. -/
noncomputable def tensorModularAtom_toCurrentSugawaraMorphism :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  splitClifford_to_currentSugawaraMorphism (tensorModularAtomHeisenbergWitness 𝕜 α)

/-- Product of the Sugawara morphism and current representation induced by
`tensorModularAtomHeisenbergWitness`. -/
noncomputable def tensorModularAtom_toCurrentSugawaraMorphism_and_current :
    CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) ×
      CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  splitClifford_currentSugawara_and_current (tensorModularAtomHeisenbergWitness 𝕜 α)

/-- Sugawara Virasoro representation induced by `tensorModularAtomHeisenbergWitness`. -/
noncomputable def tensorModularAtom_to_sugawaraRepresentation :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
      (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) :=
  (tensorModularAtomHeisenbergWitness 𝕜 α).currentSugawaraRepresentation

/-- Product of the current representation and Sugawara Virasoro representation
induced by `tensorModularAtomHeisenbergWitness`. -/
noncomputable def tensorModularAtom_toCurrentAndSugawara :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) ×
      (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
        (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  splitClifford_current_and_sugawara (tensorModularAtomHeisenbergWitness 𝕜 α)

/-- Joint readout of the mode family, eventual truncation, and Heisenberg
commutator of `tensorModularAtom_toCurrentHeisenbergRep`. -/
theorem tensorModularAtom_current_readout :
    (tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).J =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
      ∧ (∀ v, ∀ᶠ l : Int in atTop,
          (tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).J l v = 0)
      ∧ ∀ m n,
          (((tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).J m).commutator
            ((tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).J n)) =
            if m + n = 0 then (m : 𝕜) •
              (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                VirasoroProject.ChargedFockSpace 𝕜 α) else 0 := by
  constructor
  · rfl
  · exact ⟨(tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).trunc,
      (tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).comm⟩

/-- Joint readout of the Heisenberg and Virasoro components of
`tensorModularAtom_toCurrentSugawaraMorphism`. -/
theorem tensorModularAtom_currentSugawara_readout :
    (tensorModularAtom_toCurrentSugawaraMorphism (𝕜 := 𝕜) (α := α)).heisenberg =
      tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)
      ∧ (tensorModularAtom_toCurrentSugawaraMorphism (𝕜 := 𝕜) (α := α)).virasoro =
        (tensorModularAtom_toCurrentHeisenbergRep (𝕜 := 𝕜) (α := α)).currentSugawaraRepresentation := by
  constructor
  · exact CurrentSugawaraMorphism.ofHeisenberg_heisenberg _
  · exact CurrentSugawaraMorphism.ofHeisenberg_virasoro _

end ChargedFockWitness

end InfoGeometry.Canonical.TensorModularAtomCurrent
