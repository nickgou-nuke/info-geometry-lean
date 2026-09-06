/-
InfoGeometry/OperatorAlgebra/ChiralLightconeStinespring.lean

Chiral lightcone stage for the Stinespring-Tomita clinch.

This module formalizes the statement:

  observed absorption/loss is a deficit in the visible chiral lightcone branch;
  with a Stinespring-Tomita dilation witness, that deficit is accounted for by
  a mirrored hidden/environment/commutant component.

The module does not claim that every absorbing process is automatically a
commutant reflection. The commutant interpretation is supplied by a
proof-carrying calibration datum.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.OperatorAlgebra.OperatorChiralLightcone

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring

open InfoGeometry.OperatorAlgebra.StinespringDilation
open InfoGeometry.OperatorAlgebra.OperatorChiralLightcone

/-! ## 1. Algebraic chiral projector stage -/

/--
A pair of complementary chiral projectors.

`PL` and `PR` are the algebraic lightcone rails. They are complementary
idempotents, not dynamically defined by a force or channel.
-/
structure ChiralProjectorPair
    (Op : Type*) [Ring Op] where
  PL : Op
  PR : Op

  PL_idem :
    PL * PL = PL

  PR_idem :
    PR * PR = PR

  complementary :
    PL + PR = 1

  disjoint_left :
    PL * PR = 0

  disjoint_right :
    PR * PL = 0

namespace ChiralProjectorPair

variable {Op : Type*} [Ring Op]
variable (C : ChiralProjectorPair Op)

/--
Left-supported operator: algebraic left-moving/null sector.
-/
def IsLeftSupported
    (x : Op) : Prop :=
  C.PL * x = x

/--
Right-supported operator: algebraic right-moving/null sector.
-/
def IsRightSupported
    (x : Op) : Prop :=
  C.PR * x = x

/--
Lightlike/chiral support: the operator lives purely on one chiral rail.
-/
def IsChiralLightlike
    (x : Op) : Prop :=
  C.IsLeftSupported x ∨ C.IsRightSupported x

/--
A coupling is off-diagonal if it has no same-sector block.

This is the algebraic socket for mass/chiral mixing.
-/
def IsOffDiagonalCoupling
    (m : Op) : Prop :=
  C.PL * m * C.PL = 0 ∧
  C.PR * m * C.PR = 0

/--
A coupling actually mixes left and right if at least one off-diagonal block is
nonzero.
-/
def CouplesLeftRight
    (m : Op) : Prop :=
  C.PL * m * C.PR ≠ 0 ∨
  C.PR * m * C.PL ≠ 0

/--
The chiral projectors commute trivially because they are disjoint.
-/
theorem projector_commutator_zero :
    C.PL * C.PR - C.PR * C.PL = 0 := by
  rw [C.disjoint_left, C.disjoint_right]
  simp

end ChiralProjectorPair

/-! ## 2. Chiral lightcone as a carrier-stage -/

/--
A chiral lightcone stage on a real state module.

`leftCone` and `rightCone` are the visible chiral rails.

`commutantCone` is the hidden/Tomita-mirrored sector.

`mirror` is the stage-level mirror map, representing the modular/Tomita/CPT
routing at the geometric level.
-/
structure ChiralLightconeStage
    (State : Type*) [AddCommGroup State] [Module ℝ State] where
  leftCone : Set State
  rightCone : Set State
  commutantCone : Set State

  mirror : State → State

  mirror_left_to_right :
    ∀ x : State, x ∈ leftCone → mirror x ∈ rightCone

  mirror_right_to_left :
    ∀ x : State, x ∈ rightCone → mirror x ∈ leftCone

  /-- Interpretation law: the commutant cone is the hidden mirrored sector. -/
  commutant_law : Prop
  commutant_certificate :
    commutant_law

namespace ChiralLightconeStage

variable {State : Type*} [AddCommGroup State] [Module ℝ State]
variable (S : ChiralLightconeStage State)

/--
Visible chiral lightcone: union of left and right rails.
-/
def visibleCone : Set State :=
  S.leftCone ∪ S.rightCone

/--
Left states are visible.
-/
theorem left_mem_visible
    {x : State}
    (hx : x ∈ S.leftCone) :
    x ∈ S.visibleCone :=
  Or.inl hx

/--
Right states are visible.
-/
theorem right_mem_visible
    {x : State}
    (hx : x ∈ S.rightCone) :
    x ∈ S.visibleCone :=
  Or.inr hx

end ChiralLightconeStage

/-! ## 3. Visible deficit / absorption -/

/--
Observed deficit between ideal and actual open-system branches.

For an absorbing or lossy channel, this is the part missing from the visible
actual branch relative to the ideal reference branch.
-/
def visibleDeficit
    {State : Type*} [AddCommGroup State] [Module ℝ State]
    (C : OpenSystemChannel State)
    (x : State) : State :=
  C.ideal x - C.actual x

/--
A state experiences visible absorption/loss when the ideal-actual deficit is
nonzero.
-/
def HasVisibleAbsorption
    {State : Type*} [AddCommGroup State] [Module ℝ State]
    (C : OpenSystemChannel State)
    (x : State) : Prop :=
  visibleDeficit C x ≠ 0

/-! ## 4. Stinespring-Tomita clinch on the chiral lightcone -/

/--
Stinespring-Tomita clinch calibrated to a chiral lightcone stage.

The crucial field is `hidden_lands_in_commutant`: for visible lightcone states,
the hidden mirrored component supplied by the dilation lands in the commutant
cone.
-/
structure StinespringTomitaClinch
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : OpenSystemChannel State) where

  stage :
    ChiralLightconeStage State

  dilation :
    StinespringDilation State Env Joint C

  /--
  The hidden mirrored component of a visible lightcone state lands in the
  commutant cone.
  -/
  hidden_lands_in_commutant :
    ∀ x : State,
      x ∈ stage.visibleCone →
        dilation.mirroredHiddenComponent x ∈ stage.commutantCone

  /--
  Calibration law: this is the intended Tomita/Stinespring interpretation of
  absorption as hidden-sector transfer.
  -/
  clinch_law : Prop
  clinch_certificate :
    clinch_law

namespace StinespringTomitaClinch

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}

variable (K : StinespringTomitaClinch State Env Joint C)

/--
The visible deficit equals the mirrored hidden component.
-/
theorem visibleDeficit_eq_mirroredHidden
    (x : State) :
    visibleDeficit C x =
      K.dilation.mirroredHiddenComponent x := by
  dsimp [visibleDeficit]
  exact K.dilation.ideal_sub_actual_eq_mirroredHidden x

/--
Visible absorption implies a nonzero mirrored hidden component.
-/
theorem nonzero_absorption_implies_nonzero_hidden
    {x : State}
    (hx : HasVisibleAbsorption C x) :
    K.dilation.mirroredHiddenComponent x ≠ 0 := by
  intro hzero
  apply hx
  rw [K.visibleDeficit_eq_mirroredHidden x, hzero]

/--
For visible lightcone states, the mirrored hidden component lies in the
commutant cone.
-/
theorem hidden_component_in_commutant
    {x : State}
    (hx : x ∈ K.stage.visibleCone) :
    K.dilation.mirroredHiddenComponent x ∈ K.stage.commutantCone :=
  K.hidden_lands_in_commutant x hx

/--
Visible absorption of a visible lightcone state is accounted for by a nonzero
component in the commutant cone.
-/
theorem absorption_accounted_in_commutant
    {x : State}
    (hvis : x ∈ K.stage.visibleCone)
    (habs : HasVisibleAbsorption C x) :
    K.dilation.mirroredHiddenComponent x ∈ K.stage.commutantCone ∧
      K.dilation.mirroredHiddenComponent x ≠ 0 :=
  ⟨K.hidden_component_in_commutant hvis,
   K.nonzero_absorption_implies_nonzero_hidden habs⟩

end StinespringTomitaClinch

/-! ## 5. Hidden information and heat on the chiral lightcone -/

/--
A chiral-lightcone Stinespring model with hidden-information readout.

This packages the previous Stinespring dilation heat/information bridge with
the chiral lightcone commutant calibration.
-/
structure ChiralLightconeInformationConservation
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : OpenSystemChannel State) where

  bregman :
    BregmanBackend State

  hiddenReadout :
    HiddenInformationReadout Env

  clinch :
    StinespringTomitaClinch State Env Joint C

  heatHiddenBridge :
    HeatHiddenInformationBridge
      State Env Joint bregman C clinch.dilation hiddenReadout

namespace ChiralLightconeInformationConservation

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}

variable (M : ChiralLightconeInformationConservation State Env Joint C)

/--
Heat loss equals hidden information once the bridge is supplied.
-/
theorem heat_eq_hidden_information
    (x : State) :
    bregmanHeatLoss M.bregman C x =
      hiddenInformation M.clinch.dilation M.hiddenReadout x :=
  HeatHiddenInformationBridge.heat_is_hidden_information M.heatHiddenBridge x

/--
Heat loss is nonnegative.
-/
theorem heat_nonneg
    (x : State) :
    0 ≤ bregmanHeatLoss M.bregman C x :=
  HeatHiddenInformationBridge.heat_nonneg_from_hidden M.heatHiddenBridge x

/--
Visible lightcone absorption is accompanied by a nonzero hidden commutant
component.
-/
theorem visible_absorption_has_commutant_component
    {x : State}
    (hvis : x ∈ M.clinch.stage.visibleCone)
    (habs : HasVisibleAbsorption C x) :
    M.clinch.dilation.mirroredHiddenComponent x ∈
        M.clinch.stage.commutantCone ∧
      M.clinch.dilation.mirroredHiddenComponent x ≠ 0 :=
  M.clinch.absorption_accounted_in_commutant hvis habs

end ChiralLightconeInformationConservation

/-! ## 6. Conservative Stinespring accounting on chiral lightcone branches -/

/--
A chiral lightcone routing datum.

`Carrier` is the geometric carrier on which the chiral lightcones live.

`System` is the observed algebraic/state branch.

`Env` is the hidden environment/commutant branch.

The fields `visibleCarrier` and `hiddenCarrier` convert algebraic states into
carrier-level lightcone data.
-/
structure ChiralLightconeRouting
    (System Env Carrier : Type*)
    [AddCommGroup Carrier] [Module ℝ Carrier] where

  /-- Left chiral lightcone. -/
  leftCone : Set Carrier

  /-- Right chiral lightcone. -/
  rightCone : Set Carrier

  /-- Carrier readout of an observed system state. -/
  visibleCarrier : System → Carrier

  /-- Carrier readout of a hidden environment/commutant state. -/
  hiddenCarrier : Env → Carrier

  /--
  Tomita/CPT routing law:

  observed left-cone loss is routed into the hidden right-cone branch.
  -/
  left_visible_routes_to_right_hidden_law : Prop

  /-- Proof of the left-to-right routing law. -/
  left_visible_routes_to_right_hidden :
    left_visible_routes_to_right_hidden_law

  /--
  Opposite routing law:

  observed right-cone loss is routed into the hidden left-cone branch.
  -/
  right_visible_routes_to_left_hidden_law : Prop

  /-- Proof of the right-to-left routing law. -/
  right_visible_routes_to_left_hidden :
    right_visible_routes_to_left_hidden_law

/--
A stronger, directly usable chiral-lightcone routing law for a concrete
dilation.

The environment branch produced by the dilation of a left-lightcone system
state lands in the right hidden lightcone.
-/
structure LeftToRightHiddenRouting
    (System Dilated Env Carrier : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier]
    (D : StinespringInformationDilation System Dilated Env)
    (R : ChiralLightconeRouting System Env Carrier) where

  /-- Left observed branch routes into right hidden branch. -/
  hidden_right_of_visible_left :
    ∀ U : System,
      R.visibleCarrier U ∈ R.leftCone →
        R.hiddenCarrier
          (D.environmentPart (D.dilatedFlow (D.inject U))) ∈ R.rightCone

/--
Right observed branch routes into left hidden branch.
-/
structure RightToLeftHiddenRouting
    (System Dilated Env Carrier : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier]
    (D : StinespringInformationDilation System Dilated Env)
    (R : ChiralLightconeRouting System Env Carrier) where

  /-- Right observed branch routes into left hidden branch. -/
  hidden_left_of_visible_right :
    ∀ U : System,
      R.visibleCarrier U ∈ R.rightCone →
        R.hiddenCarrier
          (D.environmentPart (D.dilatedFlow (D.inject U))) ∈ R.leftCone

/--
A full chiral lightcone Stinespring-Tomita clinch.

It records:

* the conservative Stinespring accounting;
* the chiral-lightcone routing;
* the left-to-right and right-to-left hidden-sector laws.
-/
structure ChiralLightconeStinespringClinch
    (System Dilated Env Carrier : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier] where

  /-- Conservative dilation/accounting datum. -/
  dilation :
    StinespringInformationDilation System Dilated Env

  /-- Chiral lightcone routing datum. -/
  routing :
    ChiralLightconeRouting System Env Carrier

  /-- Left-to-right hidden routing law. -/
  left_to_right :
    LeftToRightHiddenRouting
      System Dilated Env Carrier dilation routing

  /-- Right-to-left hidden routing law. -/
  right_to_left :
    RightToLeftHiddenRouting
      System Dilated Env Carrier dilation routing

  /--
  Tomita/CPT calibration law.

  Intended meaning: the hidden branch is the commutant/Tomita mirror branch,
  not an arbitrary environment.
  -/
  tomita_cpt_calibration_law : Prop

  /-- Proof of the Tomita/CPT calibration law. -/
  tomita_cpt_calibration :
    tomita_cpt_calibration_law

namespace ChiralLightconeStinespringClinch

variable
    {System Dilated Env Carrier : Type*}
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier]

variable (C :
  ChiralLightconeStinespringClinch
    System Dilated Env Carrier)

/--
Accessible loss equals hidden information, by the underlying Stinespring
accounting law.
-/
theorem accessible_loss_eq_hidden_information
    (U : System) :
    C.dilation.accessibleInfo U
      - C.dilation.accessibleInfo (C.dilation.observedFlow U)
      =
    C.dilation.hiddenInfo
      (C.dilation.environmentPart
        (C.dilation.dilatedFlow (C.dilation.inject U))) :=
  C.dilation.accessible_loss_eq_hidden_information U

/--
If the observed state lies on the left chiral lightcone, the hidden branch
created by the dilation lies on the right chiral lightcone.
-/
theorem hidden_right_of_visible_left
    (U : System)
    (hU : C.routing.visibleCarrier U ∈ C.routing.leftCone) :
    C.routing.hiddenCarrier
      (C.dilation.environmentPart
        (C.dilation.dilatedFlow (C.dilation.inject U)))
      ∈ C.routing.rightCone :=
  C.left_to_right.hidden_right_of_visible_left U hU

/--
If the observed state lies on the right chiral lightcone, the hidden branch
created by the dilation lies on the left chiral lightcone.
-/
theorem hidden_left_of_visible_right
    (U : System)
    (hU : C.routing.visibleCarrier U ∈ C.routing.rightCone) :
    C.routing.hiddenCarrier
      (C.dilation.environmentPart
        (C.dilation.dilatedFlow (C.dilation.inject U)))
      ∈ C.routing.leftCone :=
  C.right_to_left.hidden_left_of_visible_right U hU

/--
A heat calibration attached to the clinch.

This turns the information-accounting law into a thermodynamic readout.
-/
structure HeatCalibration where
  /-- Heat readout of an observed system state. -/
  heat : System → ℝ

  /-- Heat is calibrated as accessible distinguishability loss. -/
  heat_eq_accessible_loss :
    ∀ U : System,
      heat U =
        C.dilation.accessibleInfo U
          - C.dilation.accessibleInfo (C.dilation.observedFlow U)

namespace HeatCalibration

variable (H : C.HeatCalibration)

/--
Heat equals hidden information once the heat calibration is supplied.
-/
theorem heat_eq_hidden_information
    (U : System) :
    H.heat U =
      C.dilation.hiddenInfo
        (C.dilation.environmentPart
          (C.dilation.dilatedFlow (C.dilation.inject U))) := by
  rw [H.heat_eq_accessible_loss U]
  exact C.accessible_loss_eq_hidden_information U

end HeatCalibration

/--
A Bregman calibration attached to the clinch.

This says the observed heat is the oriented Bregman shear between an ideal
lossless branch and the actual observed branch.
-/
structure BregmanCalibration where
  /-- Ideal lossless comparison branch. -/
  idealFlow : System →L[ℝ] System

  /-- Bregman divergence/readout. -/
  bregman : System → System → ℝ

  /-- Bregman divergence is nonnegative. -/
  bregman_nonneg :
    ∀ X Y : System, 0 ≤ bregman X Y

  /-- Heat/Bregman calibration. -/
  bregman_eq_accessible_loss :
    ∀ U : System,
      bregman (idealFlow U) (C.dilation.observedFlow U)
        =
      C.dilation.accessibleInfo U
        - C.dilation.accessibleInfo (C.dilation.observedFlow U)

namespace BregmanCalibration

variable (B : C.BregmanCalibration)

/--
Bregman heat is nonnegative.
-/
theorem bregman_heat_nonneg
    (U : System) :
    0 ≤ B.bregman (B.idealFlow U) (C.dilation.observedFlow U) :=
  B.bregman_nonneg _ _

/--
Bregman heat equals hidden commutant/lightcone information.
-/
theorem bregman_heat_eq_hidden_information
    (U : System) :
    B.bregman (B.idealFlow U) (C.dilation.observedFlow U)
      =
    C.dilation.hiddenInfo
      (C.dilation.environmentPart
        (C.dilation.dilatedFlow (C.dilation.inject U))) := by
  rw [B.bregman_eq_accessible_loss U]
  exact C.accessible_loss_eq_hidden_information U

end BregmanCalibration

end ChiralLightconeStinespringClinch

/-! ## 7. Owner target -/

/--
Owner target for installing a chiral-lightcone Stinespring-Tomita clinch.
-/
def ChiralLightconeStinespringOwnerTarget
    (System Dilated Env Carrier : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier] : Prop :=
  Nonempty
    (ChiralLightconeStinespringClinch
      System Dilated Env Carrier)

end InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring
