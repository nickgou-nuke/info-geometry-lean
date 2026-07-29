import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/-!
InfoGeometry/OperatorAlgebra/DrazinEntropyFunctional.lean

Drazin entropy functional.

This module formalizes the conservative statement:

* Drazin data separate a regular/stable readout from nilpotent residue data;
* entropy is not produced by Drazin inversion alone;
* entropy is obtained only after a supplied stable-volume, trace, or finite
  microstate-count calibration.

No Moore--Penrose theorem, Drazin existence theorem, Wedderburn--Artin theorem,
Dubrovin semisimplicity theorem, or Gromov--Witten localization theorem is
asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

open DrazinProjectionLocalization

/--
A stable Drazin readout over a state space.

`regularPart`, `nilpotentResidue`, and `drazinInverse` are intentionally carried
as data. The law fields are proposition-valued predicates tied to the state and
are accompanied by explicit proofs on valid states.
-/
structure DrazinStableReadout (Op State : Type*) [Add Op] [Mul Op] where
  /-- Operator or algebra element attached to a state. -/
  elementOf : State -> Op
  /-- Stable regular component extracted by the model. -/
  regularPart : State -> Op
  /-- Nilpotent or singular residue component retained by the model. -/
  nilpotentResidue : State -> Op
  /-- Drazin inverse/readout for the state operator. -/
  drazinInverse : State -> Op
  /-- Stable volume/weight retained after Drazin regularization. -/
  stableVolume : State -> ℝ
  /-- Validity predicate for states to which the calibration applies. -/
  valid : State -> Prop
  /-- The stable volume is positive on valid states. -/
  stableVolume_pos : ∀ s : State, valid s -> 0 < stableVolume s
  /-- The regular and residue readouts reconstruct the attached element. -/
  decompositionLaw :
    ∀ s : State, valid s ->
      elementOf s = regularPart s + nilpotentResidue s
  /-- The readout inverse satisfies the noncommutative Drazin laws. -/
  drazinLaw :
    ∀ s : State, valid s ->
      (drazinInverse s * elementOf s = elementOf s * drazinInverse s) ∧
        (drazinInverse s * elementOf s * drazinInverse s = drazinInverse s)

namespace DrazinStableReadout

variable {Op State : Type*} [Add Op] [Mul Op]

/-- The supplied decomposition proof is available on valid states. -/
theorem decomposition_holds_readback
    (D : DrazinStableReadout Op State)
    (s : State) (hs : D.valid s) :
    D.elementOf s = D.regularPart s + D.nilpotentResidue s :=
  D.decompositionLaw s hs

/-- The supplied Drazin proof is available on valid states. -/
theorem drazin_holds_readback
    (D : DrazinStableReadout Op State)
    (s : State) (hs : D.valid s) :
    (D.drazinInverse s * D.elementOf s =
        D.elementOf s * D.drazinInverse s) ∧
      (D.drazinInverse s * D.elementOf s * D.drazinInverse s =
        D.drazinInverse s) :=
  D.drazinLaw s hs

/-- The stable Drazin volume is nonzero on valid states. -/
theorem stableVolume_ne_zero
    (D : DrazinStableReadout Op State)
    (s : State) (hs : D.valid s) :
    D.stableVolume s ≠ 0 :=
  (D.stableVolume_pos s hs).ne'

end DrazinStableReadout

/-! ## Algebraic refinement -/

/--
Algebraic refinement of `DrazinStableReadout`.

This optional layer ties the thermodynamic/readout socket to actual
`DrazinInverseData` for the operator attached to each valid state.
-/
structure AlgebraicDrazinStableReadout
    (Op State : Type*) [Ring Op] extends DrazinStableReadout Op State where
  /-- Actual Drazin inverse data for the state operator on valid states. -/
  drazinDataOf :
    ∀ s : State, valid s -> DrazinInverseData Op
  /-- The Drazin data element is the state operator. -/
  drazinData_element_eq :
    ∀ s hs, (drazinDataOf s hs).element = elementOf s
  /-- The Drazin data inverse is the readout inverse. -/
  drazinData_inverse_eq :
    ∀ s hs, (drazinDataOf s hs).drazinInverse = drazinInverse s

namespace AlgebraicDrazinStableReadout

variable {Op State : Type*} [Ring Op]
variable (D : AlgebraicDrazinStableReadout Op State)

/-- The readout inverse commutes with the attached state operator. -/
theorem element_mul_drazinInverse_commutes
    (s : State) (hs : D.valid s) :
    D.elementOf s * D.drazinInverse s =
      D.drazinInverse s * D.elementOf s := by
  have h := (D.drazinDataOf s hs).commutes
  simpa [D.drazinData_element_eq s hs, D.drazinData_inverse_eq s hs] using h

/-- Left support law inherited from the underlying Drazin data. -/
theorem element_mul_drazinInverse_eq_support
    (s : State) (hs : D.valid s) :
    D.elementOf s * D.drazinInverse s =
      (D.drazinDataOf s hs).support := by
  have h := (D.drazinDataOf s hs).element_mul_inverse_eq_support
  simpa [D.drazinData_element_eq s hs, D.drazinData_inverse_eq s hs] using h

/-- Right support law inherited from the underlying Drazin data. -/
theorem drazinInverse_mul_element_eq_support
    (s : State) (hs : D.valid s) :
    D.drazinInverse s * D.elementOf s =
      (D.drazinDataOf s hs).support := by
  have h := (D.drazinDataOf s hs).inverse_mul_element_eq_support
  simpa [D.drazinData_element_eq s hs, D.drazinData_inverse_eq s hs] using h

/-- Reflexive Drazin law inherited from the underlying Drazin data. -/
theorem drazinInverse_reflexive
    (s : State) (hs : D.valid s) :
    D.drazinInverse s * D.elementOf s * D.drazinInverse s =
      D.drazinInverse s := by
  have h := (D.drazinDataOf s hs).inverse_element_inverse
  simpa [D.drazinData_element_eq s hs, D.drazinData_inverse_eq s hs] using h

end AlgebraicDrazinStableReadout

/--
Drazin entropy functional.

The entropy law is a calibration: the Drazin layer supplies a stable volume, and
this structure supplies the thermodynamic convention `S = k_B log W_D`.
-/
structure DrazinEntropyFunctional (Op State : Type*) [Add Op] [Mul Op] where
  /-- Drazin stable regularization readout. -/
  readout : DrazinStableReadout Op State
  /-- Boltzmann constant or unit-normalization scalar. -/
  kB : ℝ
  /-- Positivity of the entropy normalization. -/
  kB_pos : 0 < kB
  /-- Entropy readout. -/
  entropy : State -> ℝ
  /-- Entropy is calibrated by the logarithm of the stable Drazin volume. -/
  entropy_eq_kB_log_stableVolume :
    ∀ s : State, readout.valid s ->
      entropy s = kB * Real.log (readout.stableVolume s)

namespace DrazinEntropyFunctional

variable {Op State : Type*} [Add Op] [Mul Op]
variable (F : DrazinEntropyFunctional Op State)

/-- Re-export of the Drazin entropy calibration law. -/
theorem entropy_eq_kB_log_volume
    (s : State) (hs : F.readout.valid s) :
    F.entropy s = F.kB * Real.log (F.readout.stableVolume s) :=
  F.entropy_eq_kB_log_stableVolume s hs

/-- Entropy is nonnegative when the stable Drazin volume is at least one. -/
theorem entropy_nonneg_of_one_le_stableVolume
    (s : State) (hs : F.readout.valid s)
    (hvol : 1 ≤ F.readout.stableVolume s) :
    0 ≤ F.entropy s := by
  rw [F.entropy_eq_kB_log_volume s hs]
  exact mul_nonneg F.kB_pos.le (Real.log_nonneg hvol)

/-- The stable volume is positive on valid states. -/
theorem stableVolume_pos
    (s : State) (hs : F.readout.valid s) :
    0 < F.readout.stableVolume s :=
  F.readout.stableVolume_pos s hs

end DrazinEntropyFunctional

/--
Finite microstate calibration for Drazin entropy.

This is the finite Boltzmann-counting version: the stable Drazin volume is the
cardinality of a supplied finite microstate fiber.
-/
structure FiniteDrazinMicrostateCalibration
    (Op State MicroState : Type*) [Add Op] [Mul Op] where
  /-- Drazin entropy functional. -/
  functional : DrazinEntropyFunctional Op State
  /-- Finite microstate fiber assigned to each state. -/
  microstatesOf : State -> Finset MicroState
  /-- Stable Drazin volume equals microstate count on valid states. -/
  stableVolume_eq_card :
    ∀ s : State, functional.readout.valid s ->
      functional.readout.stableVolume s = ((microstatesOf s).card : ℝ)
  /-- Microstate fibers are nonempty on valid states. -/
  microstates_nonempty :
    ∀ s : State, functional.readout.valid s -> (microstatesOf s).Nonempty

namespace FiniteDrazinMicrostateCalibration

variable {Op State MicroState : Type*} [Add Op] [Mul Op]
variable (C : FiniteDrazinMicrostateCalibration Op State MicroState)

/-- The calibrated Drazin entropy is `k_B log` of the finite microstate count. -/
theorem entropy_eq_kB_log_card
    (s : State) (hs : C.functional.readout.valid s) :
    C.functional.entropy s =
      C.functional.kB * Real.log ((C.microstatesOf s).card : ℝ) := by
  calc
    C.functional.entropy s
        = C.functional.kB * Real.log (C.functional.readout.stableVolume s) :=
            C.functional.entropy_eq_kB_log_volume s hs
    _ = C.functional.kB * Real.log ((C.microstatesOf s).card : ℝ) := by
            rw [C.stableVolume_eq_card s hs]

/-- Finite Drazin entropy is nonnegative on valid states. -/
theorem entropy_nonneg
    (s : State) (hs : C.functional.readout.valid s) :
    0 ≤ C.functional.entropy s := by
  rw [C.entropy_eq_kB_log_card s hs]
  have hcardNat : 0 < (C.microstatesOf s).card := by
    exact Finset.card_pos.mpr (C.microstates_nonempty s hs)
  have hcard : (1 : ℝ) ≤ ((C.microstatesOf s).card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hcardNat
  exact mul_nonneg C.functional.kB_pos.le (Real.log_nonneg hcard)

end FiniteDrazinMicrostateCalibration

/--
Spectral/GW-volume calibration for Drazin entropy.

`gwVolume` is a model-specific localized Gromov--Witten volume or virtual-count
readout. The equality to the stable Drazin volume is supplied as calibration
data, not derived here.
-/
structure DrazinGWVolumeCalibration (Op State : Type*) [Add Op] [Mul Op] where
  functional : DrazinEntropyFunctional Op State
  gwVolume : State -> ℝ
  gwVolume_eq_stableVolume :
    ∀ s : State, functional.readout.valid s ->
      gwVolume s = functional.readout.stableVolume s

namespace DrazinGWVolumeCalibration

variable {Op State : Type*} [Add Op] [Mul Op]
variable (C : DrazinGWVolumeCalibration Op State)

/-- Drazin entropy expressed through the calibrated GW volume. -/
theorem entropy_eq_kB_log_gwVolume
    (s : State) (hs : C.functional.readout.valid s) :
    C.functional.entropy s =
      C.functional.kB * Real.log (C.gwVolume s) := by
  calc
    C.functional.entropy s
        = C.functional.kB * Real.log (C.functional.readout.stableVolume s) :=
            C.functional.entropy_eq_kB_log_volume s hs
    _ = C.functional.kB * Real.log (C.gwVolume s) := by
            rw [C.gwVolume_eq_stableVolume s hs]

end DrazinGWVolumeCalibration

/--
Operator-information extraction tied directly to the Drazin readout.

The extracted stable component is explicitly the regular part, and the
singular component is explicitly the nilpotent residue.  This avoids arbitrary
proposition-valued law sockets that would not add mathematical content.
-/
structure DrazinInformationExtraction (Op State : Type*) [Add Op] [Mul Op] where
  readout : DrazinStableReadout Op State
  stableInformation : State -> Op
  singularResidue : State -> Op
  stableInformation_eq_regularPart :
    ∀ s : State, readout.valid s ->
      stableInformation s = readout.regularPart s
  singularResidue_eq_nilpotentResidue :
    ∀ s : State, readout.valid s ->
      singularResidue s = readout.nilpotentResidue s

namespace DrazinInformationExtraction

variable {Op State : Type*} [Add Op] [Mul Op]
variable (P : DrazinInformationExtraction Op State)

/-- Stable information is the regular Drazin readout on valid states. -/
theorem stableInformation_eq_regularPart_readback
    (s : State) (hs : P.readout.valid s) :
    P.stableInformation s = P.readout.regularPart s :=
  P.stableInformation_eq_regularPart s hs

/-- Singular residue is the nilpotent Drazin readout on valid states. -/
theorem singularResidue_eq_nilpotentResidue_readback
    (s : State) (hs : P.readout.valid s) :
    P.singularResidue s = P.readout.nilpotentResidue s :=
  P.singularResidue_eq_nilpotentResidue s hs

end DrazinInformationExtraction

end InfoGeometry.OperatorAlgebra
