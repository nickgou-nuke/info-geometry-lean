/-
InfoGeometry/OperatorAlgebra/ChiralTubuleBoundary.lean

Chiral tubule boundary and topological snap.

This module packages the capstone boundary event:

  Hessian rank collapse
    + extreme shear threshold
    + conserved topological obstruction
    + chiral lightcone support
    ⇒ stable chiral residue / tubule boundary witness.

The Unruh temperature may drive the threshold once a modular acceleration
calibration is supplied, but temperature alone is not the snap theorem.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.SusceptibilityHessian
import InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
import InfoGeometry.OperatorAlgebra.TopologicalSnap
import InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
import InfoGeometry.OperatorAlgebra.BrewsterDrazinIntersection
import InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring
import InfoGeometry.OperatorAlgebra.StinespringTomitaLightcone
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralTubuleBoundary

open InfoGeometry.OperatorAlgebra.SusceptibilityHessian
open InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
open InfoGeometry.OperatorAlgebra.TopologicalSnap
open InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
open InfoGeometry.OperatorAlgebra.BrewsterDrazinIntersection
open InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring

/-! ## 1. Hessian collapse and extreme shear -/

/--
A Hessian collapse event.

This is the abstract socket for the point where the Bregman/information Hessian
ceases to define a locally invertible material/vacuum response.
-/
structure HessianCollapseEvent
    (State Tangent : Type*) where
  /-- State at which the response degenerates. -/
  state : State

  /-- Degenerating tangent/response direction. -/
  nullDirection : Tangent

  /-- The Hessian vanishes or collapses along the chosen direction. -/
  hessian_collapse : Prop

  /-- Rank-defect / loss-of-invertibility certificate. -/
  rank_defect : Prop

/--
A scalar shear readout.

Concrete models may instantiate this by a Bregman divergence, Hessian
condition number, modular acceleration, absorption coefficient, or curvature
readout.
-/
structure ShearReadout
    (State : Type*) where
  shear : State → ℝ

/-- An extreme shear threshold. -/
structure ExtremeShearThreshold
    (State : Type*) where
  readout : ShearReadout State

  /-- Critical threshold. -/
  threshold : ℝ

  /-- Threshold is nonnegative. -/
  threshold_nonneg : 0 ≤ threshold

/-- A state crosses the extreme shear threshold. -/
def CrossesShearThreshold
    {State : Type*}
    (Theta : ExtremeShearThreshold State)
    (X : State) : Prop :=
  Theta.threshold ≤ Theta.readout.shear X

namespace ExtremeShearThreshold

variable {State : Type*}
variable (Theta : ExtremeShearThreshold State)

/-- Named theorem form of threshold crossing. -/
theorem crosses_iff
    (X : State) :
    CrossesShearThreshold Theta X ↔
      Theta.threshold ≤ Theta.readout.shear X :=
  Iff.rfl

end ExtremeShearThreshold

/-! ## 2. Unruh-driven shear calibration -/

/--
A calibration saying that the Unruh/modular temperature drives the chosen
shear readout.

This does not say that temperature alone creates a residue. It only connects
the modular acceleration scale to the shear threshold.
-/
structure UnruhShearCalibration
    (State : Type*) where
  /-- Modular acceleration/temperature calibration. -/
  unruh : ModularAccelerationCalibration

  /-- Shear threshold. -/
  threshold : ExtremeShearThreshold State

  /-- State being driven. -/
  drivenState : State

  /--
  Temperature crosses the critical scale.

  Concrete modules may replace this by a dimensional inequality involving
  material constants, gap scale, susceptibility, or chemical potential.
  -/
  temperature_crosses_threshold :
    threshold.threshold ≤ unruh.temperature

  /-- The thermal drive is calibrated to the chosen shear readout. -/
  temperature_drives_shear :
    unruh.temperature ≤ threshold.readout.shear drivenState

namespace UnruhShearCalibration

variable {State : Type*}
variable (U : UnruhShearCalibration State)

/-- The Unruh-calibrated drive crosses the shear threshold. -/
theorem driven_state_crosses_shear_threshold :
    CrossesShearThreshold U.threshold U.drivenState := by
  exact le_trans U.temperature_crosses_threshold U.temperature_drives_shear

/-- The Unruh temperature has its natural-unit value. -/
theorem unruh_temperature :
    U.unruh.temperature =
      U.unruh.acceleration / (2 * Real.pi) :=
  U.unruh.unruh_temperature

end UnruhShearCalibration

/-! ## 3. Topological obstruction and chiral residue -/

/--
A topological obstruction attached to a state.

`Charge` may be `ℤ`, `ZMod 2`, `ZMod 16`, a determinant-sign charge, or a
more refined anomaly index.
-/
structure TopologicalObstruction
    (State Charge : Type*) [Zero Charge] where
  invariant : State → Charge

  /-- Flat/trivial sector. -/
  flatSector : Set State

  /-- Flat states have zero obstruction. -/
  flat_invariant_zero :
    ∀ X : State, X ∈ flatSector → invariant X = 0

  /-- A nonzero obstruction prevents membership in the flat sector. -/
  nontrivial_at :
    ∀ X : State, invariant X ≠ 0 → X ∉ flatSector

namespace TopologicalObstruction

variable {State Charge : Type*} [Zero Charge]
variable (O : TopologicalObstruction State Charge)

/-- A nonzero obstruction prevents membership in the flat sector. -/
theorem not_flat_of_nonzero
    {X : State}
    (hX : O.invariant X ≠ 0) :
    X ∉ O.flatSector :=
  O.nontrivial_at X hX

end TopologicalObstruction

/--
A stable chiral residue.

This is the abstract “Majorana-Weyl/tubule residue” socket. It is not derived
from temperature alone. It is attached after the snap boundary has been
calibrated.
-/
structure ChiralResidue
    (State Residue : Type*) where
  /-- State at which the residue is formed. -/
  state : State

  /-- Residue object. -/
  residue : Residue

  /-- Majorana-Weyl / DIII / chiral-sector certificate, depending on model. -/
  chiral_residue_certificate : Prop

  /-- Stability law. -/
  stable : Prop

  /-- Evidence for stability. -/
  stable_certificate :
    stable

/-! ## 4. Chiral tubule boundary witness -/

/--
The capstone boundary event.

A chiral tubule boundary occurs when:

* the information/material Hessian collapses;
* the shear threshold is crossed;
* a conserved obstruction prevents flattening;
* the boundary readout lies on a chiral lightcone sector;
* a stable chiral residue is produced.
-/
structure ChiralTubuleBoundaryWitness
    (State Tangent Charge Residue H : Type*)
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H) where

  /-- Hessian/rank collapse. -/
  collapse : HessianCollapseEvent State Tangent

  /-- Extreme shear threshold. -/
  threshold : ExtremeShearThreshold State

  /-- Threshold crossing at the collapse state. -/
  crosses_threshold :
    CrossesShearThreshold threshold collapse.state

  /-- Topological obstruction. -/
  obstruction : TopologicalObstruction State Charge

  /-- The collapse state has nonzero obstruction. -/
  obstruction_nonzero :
    obstruction.invariant collapse.state ≠ 0

  /-- Carrier readout of the boundary state. -/
  carrierReadout : State → H

  /-- Chiral side selected at the snap boundary. -/
  side : ChiralSide

  /-- The boundary carrier readout is on the selected chiral lightcone. -/
  boundary_on_chiral_lightcone :
    carrierReadout collapse.state ∈ ChiralLightcone Q C side

  /-- Stable chiral residue produced by the snap. -/
  residue : ChiralResidue State Residue

  /-- The residue belongs to the collapse state. -/
  residue_at_collapse :
    residue.state = collapse.state

namespace ChiralTubuleBoundaryWitness

variable
    {State Tangent Charge Residue H : Type*}
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H]
    {Q : KreinIsotropicCone.KreinQuadraticDatum H}
    {C : ModuleCircularPolarization H}

variable
    (B : ChiralTubuleBoundaryWitness
      State Tangent Charge Residue H Q C)

/-- The snap state cannot be flat. -/
theorem collapse_state_not_flat :
    B.collapse.state ∉ B.obstruction.flatSector :=
  B.obstruction.not_flat_of_nonzero B.obstruction_nonzero

/-- The snap state lies on the selected chiral lightcone after carrier readout. -/
theorem collapse_state_on_chiral_lightcone :
    B.carrierReadout B.collapse.state ∈
      ChiralLightcone Q C B.side :=
  B.boundary_on_chiral_lightcone

/-- The snap state crosses the extreme shear threshold. -/
theorem collapse_state_crosses_threshold :
    CrossesShearThreshold B.threshold B.collapse.state :=
  B.crosses_threshold

/-- A stable chiral residue exists at the collapse boundary. -/
theorem exists_stable_chiral_residue :
    ∃ r : Residue,
      r = B.residue.residue ∧ B.residue.stable :=
  ⟨B.residue.residue, rfl, B.residue.stable_certificate⟩

end ChiralTubuleBoundaryWitness

/-! ## 5. Unruh-driven chiral tubule snap -/

/--
A chiral tubule boundary whose shear threshold is driven by a modular/Unruh
temperature calibration.

This is the precise formal version of:

“the Unruh drive is high enough to cross the extreme shear threshold, and the
already-present topological obstruction forces a stable chiral residue.”
-/
structure UnruhDrivenChiralTubuleBoundary
    (State Tangent Charge Residue H : Type*)
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H) where

  /-- Underlying chiral tubule boundary witness. -/
  boundary :
    ChiralTubuleBoundaryWitness
      State Tangent Charge Residue H Q C

  /-- Unruh/modular drive calibration. -/
  unruhShear :
    UnruhShearCalibration State

  /-- The Unruh-driven state is the collapse state. -/
  driven_eq_collapse :
    unruhShear.drivenState = boundary.collapse.state

  /-- The boundary threshold is the threshold crossed by the Unruh drive. -/
  threshold_eq :
    unruhShear.threshold = boundary.threshold

namespace UnruhDrivenChiralTubuleBoundary

variable
    {State Tangent Charge Residue H : Type*}
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H]
    {Q : KreinIsotropicCone.KreinQuadraticDatum H}
    {C : ModuleCircularPolarization H}

variable
    (U : UnruhDrivenChiralTubuleBoundary
      State Tangent Charge Residue H Q C)

/-- The Unruh drive crosses the same threshold as the chiral tubule boundary. -/
theorem unruh_crosses_boundary_threshold :
    CrossesShearThreshold U.boundary.threshold U.boundary.collapse.state := by
  have hU :
      CrossesShearThreshold
        U.unruhShear.threshold
        U.unruhShear.drivenState :=
    U.unruhShear.driven_state_crosses_shear_threshold
  rwa [U.threshold_eq, U.driven_eq_collapse] at hU

/-- The Unruh-driven boundary still has a non-flat topological obstruction. -/
theorem collapse_state_not_flat :
    U.boundary.collapse.state ∉ U.boundary.obstruction.flatSector :=
  U.boundary.collapse_state_not_flat

/-- The Unruh-driven snap produces a stable chiral residue. -/
theorem exists_stable_chiral_residue :
    ∃ r : Residue,
      r = U.boundary.residue.residue ∧ U.boundary.residue.stable :=
  U.boundary.exists_stable_chiral_residue

/-- The physical temperature in natural units is `a / 2π`. -/
theorem unruh_temperature :
    U.unruhShear.unruh.temperature =
      U.unruhShear.unruh.acceleration / (2 * Real.pi) :=
  U.unruhShear.unruh_temperature

end UnruhDrivenChiralTubuleBoundary

/-! ## 5a. Nonvacuous existing-owner snap bridges -/

/--
Topological snap boundary backed directly by `TopologicalSnap`.

This is not a new obstruction theory.  It is a named use of the existing
`ConservedObstructionFlow` theorem surface.
-/
structure ConservedSnapBoundary
    (State Charge : Type*) [Zero Charge] where
  /-- Existing conserved-obstruction flow owner. -/
  flow :
    ConservedObstructionFlow State Charge

  /-- State at the snap boundary. -/
  state : State

  /-- The selected state has nonzero conserved obstruction. -/
  obstruction_nonzero :
    flow.invariant state ≠ 0

namespace ConservedSnapBoundary

variable {State Charge : Type*} [Zero Charge]
variable (S : ConservedSnapBoundary State Charge)

/-- The snap state is not in the flat sector, by `TopologicalSnap`. -/
theorem state_not_flat :
    S.state ∉ S.flow.Flat :=
  S.flow.nontrivial_not_flat S.obstruction_nonzero

/-- The snap state cannot relax into the flat sector at any admissible time. -/
theorem cannot_flow_to_flat
    (t : ℝ) :
    S.flow.flow t S.state ∉ S.flow.Flat :=
  S.flow.nontrivial_cannot_flow_to_flat S.obstruction_nonzero t

/-- There is no finite-time flattening of any nontrivial sector in this flow. -/
theorem no_nontrivial_flattening :
    ¬ ∃ (x : State) (t : ℝ),
      S.flow.IsNontrivial x ∧ S.flow.flow t x ∈ S.flow.Flat :=
  S.flow.no_nontrivial_flattening

end ConservedSnapBoundary

/--
Brewster/Drazin rank-collapse boundary backed by
`BrewsterDrazinIntersection`.
-/
structure BrewsterDrazinBoundary
    (Op : Type*) [Ring Op] where
  /-- Existing Brewster/Drazin calibration owner. -/
  calibration :
    BrewsterDrazinCalibration Op

namespace BrewsterDrazinBoundary

variable {Op : Type*} [Ring Op]
variable (B : BrewsterDrazinBoundary Op)

/-- The calibrated Brewster event has vanishing p/second coefficient. -/
theorem rp_eq_zero :
    B.calibration.event.secondCoeff = 0 :=
  B.calibration.rp_eq_zero

/-- The nil/p-channel sector is killed by the reflection operator. -/
theorem killed_sector :
    B.calibration.split.R * B.calibration.split.Pnil = 0 :=
  B.calibration.killed_sector

/-- The Drazin/core inverse recovers the surviving core projector. -/
theorem reflected_core_identity :
    B.calibration.split.R * B.calibration.split.RD =
      B.calibration.split.Pcore :=
  B.calibration.reflected_core_identity

end BrewsterDrazinBoundary

/--
Chiral-lightcone Stinespring boundary backed by the existing conservative
Stinespring accounting and chiral routing theorems.
-/
structure ChiralLightconeStinespringBoundary
    (System Dilated Env Carrier : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier] where
  /-- Existing chiral-lightcone Stinespring clinch owner. -/
  clinch :
    ChiralLightconeStinespringClinch System Dilated Env Carrier

namespace ChiralLightconeStinespringBoundary

variable
    {System Dilated Env Carrier : Type*}
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]
    [AddCommGroup Carrier] [Module ℝ Carrier]

variable (B : ChiralLightconeStinespringBoundary System Dilated Env Carrier)

/-- Accessible loss equals hidden information by the existing Stinespring clinch. -/
theorem accessible_loss_eq_hidden_information
    (U : System) :
    B.clinch.dilation.accessibleInfo U
        - B.clinch.dilation.accessibleInfo (B.clinch.dilation.observedFlow U)
      =
      B.clinch.dilation.hiddenInfo
        (B.clinch.dilation.environmentPart
          (B.clinch.dilation.dilatedFlow (B.clinch.dilation.inject U))) :=
  B.clinch.accessible_loss_eq_hidden_information U

/-- Visible left-cone states route into the right hidden cone. -/
theorem hidden_right_of_visible_left
    (U : System)
    (hU : B.clinch.routing.visibleCarrier U ∈ B.clinch.routing.leftCone) :
    B.clinch.routing.hiddenCarrier
      (B.clinch.dilation.environmentPart
        (B.clinch.dilation.dilatedFlow (B.clinch.dilation.inject U)))
      ∈ B.clinch.routing.rightCone :=
  B.clinch.hidden_right_of_visible_left U hU

/-- Visible right-cone states route into the left hidden cone. -/
theorem hidden_left_of_visible_right
    (U : System)
    (hU : B.clinch.routing.visibleCarrier U ∈ B.clinch.routing.rightCone) :
    B.clinch.routing.hiddenCarrier
      (B.clinch.dilation.environmentPart
        (B.clinch.dilation.dilatedFlow (B.clinch.dilation.inject U)))
      ∈ B.clinch.routing.leftCone :=
  B.clinch.hidden_left_of_visible_right U hU

end ChiralLightconeStinespringBoundary

/--
Local-loss boundary backed directly by the existing
`StinespringTomitaChiralLightconeDilation` theorem surface.
-/
structure TomitaChiralLocalLossBoundary
    (Op GlobalOp H : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H)
    (Phi : StinespringTomitaLightcone.LocalChannel Op) where
  /-- Existing Stinespring/Tomita chiral-lightcone owner. -/
  dilation :
    StinespringTomitaLightcone.StinespringTomitaChiralLightconeDilation
      Op GlobalOp H Q C Phi

  /-- Locally lost observable. -/
  observable : Op

  /-- Local loss hypothesis for the observable. -/
  locally_lost :
    Phi.IsLocallyLost observable

namespace TomitaChiralLocalLossBoundary

variable
    {Op GlobalOp H : Type*}
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    {Q : KreinIsotropicCone.KreinQuadraticDatum H}
    {C : ModuleCircularPolarization H}
    {Phi : StinespringTomitaLightcone.LocalChannel Op}

variable (B : TomitaChiralLocalLossBoundary Op GlobalOp H Q C Phi)

/-- The locally lost observable is routed into the Tomita commutant. -/
theorem locally_lost_global_in_commutant :
    B.dilation.dilation.globalEvolution
        (B.dilation.dilation.embed B.observable) ∈
      B.dilation.dilation.tomita.Mcomm :=
  B.dilation.locally_lost_global_in_commutant B.locally_lost

/-- The locally lost observable has a chiral-lightcone leakage readout. -/
theorem locally_lost_has_chiral_lightcone_readout :
    ∃ side : ChiralSide,
      B.dilation.carrierReadout
          (B.dilation.dilation.leakage B.observable) ∈
        ChiralLightcone Q C side :=
  B.dilation.locally_lost_has_chiral_lightcone_readout B.locally_lost

/--
The locally lost observable is simultaneously commutant-routed and
chiral-lightlike after carrier readout.
-/
theorem locally_lost_is_commutant_chiral_lightcone :
    B.dilation.dilation.globalEvolution
        (B.dilation.dilation.embed B.observable) ∈
        B.dilation.dilation.tomita.Mcomm ∧
      ∃ side : ChiralSide,
        B.dilation.carrierReadout
            (B.dilation.dilation.leakage B.observable) ∈
          ChiralLightcone Q C side :=
  B.dilation.locally_lost_is_commutant_chiral_lightcone B.locally_lost

end TomitaChiralLocalLossBoundary

/-! ## 6. Brewster / Jones event as a rank-collapse socket -/

/--
A Jones/Fresnel rank-collapse event.

For example, a Brewster event is modeled by the vanishing of the p-polarized
reflection eigenvalue.
-/
structure JonesRankCollapseEvent
    (Freq : Type*) where
  fresnel :
    FresnelEigenCalibration Freq

  frequency : Freq

  /-- p-channel collapse, e.g. Brewster reflection zero. -/
  p_channel_zero :
    fresnel.eigenResponse.eigenvalue PolarizationMode.p frequency = 0

  /-- Optional s-channel noncollapse certificate. -/
  s_channel_nonzero : Prop

namespace JonesRankCollapseEvent

variable {Freq : Type*}
variable (J : JonesRankCollapseEvent Freq)

/-- At a Jones/Brewster rank-collapse event, the p-eigenvalue vanishes. -/
theorem p_eigenvalue_eq_zero :
    J.fresnel.eigenResponse.eigenvalue
      PolarizationMode.p J.frequency = 0 :=
  J.p_channel_zero

/-- The same event says the Fresnel `r_p` coefficient vanishes. -/
theorem r_p_eq_zero :
    J.fresnel.fresnel.r_p J.frequency = 0 := by
  have h :=
    J.fresnel.p_eigenvalue_is_r_p J.frequency
  rw [← h]
  exact J.p_channel_zero

end JonesRankCollapseEvent

/-! ## 7. Owner targets -/

/--
Compatibility predicate for constructing a chiral tubule boundary.

Concrete models should replace this by assumptions on Hessian collapse,
susceptibility response, conserved obstruction, and chiral lightcone support.
-/
def ChiralTubuleBoundaryCompatibility
    (_State _Tangent Charge _Residue H : Type*)
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H]
    (_Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (_C : ModuleCircularPolarization H) : Prop :=
  True

/-- Owner target for constructing the chiral tubule boundary witness. -/
@[owner_target_tag]
def ChiralTubuleBoundaryOwnerTarget : Prop :=
  ∀ (State Tangent Charge Residue H : Type*)
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H],
  ∀ (Q : KreinIsotropicCone.KreinQuadraticDatum H),
  ∀ (C : ModuleCircularPolarization H),
    ChiralTubuleBoundaryCompatibility State Tangent Charge Residue H Q C →
      Nonempty
        (ChiralTubuleBoundaryWitness
          State Tangent Charge Residue H Q C)

/--
Compatibility predicate for constructing an Unruh-driven chiral tubule
boundary.
-/
def UnruhDrivenChiralTubuleCompatibility
    (_State _Tangent Charge _Residue H : Type*)
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H]
    (_Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (_C : ModuleCircularPolarization H) : Prop :=
  True

/-- Owner target for the Unruh-driven boundary theorem. -/
@[owner_target_tag]
def UnruhDrivenChiralTubuleOwnerTarget : Prop :=
  ∀ (State Tangent Charge Residue H : Type*)
    [Zero Charge]
    [AddCommGroup H] [Module ℝ H],
  ∀ (Q : KreinIsotropicCone.KreinQuadraticDatum H),
  ∀ (C : ModuleCircularPolarization H),
    UnruhDrivenChiralTubuleCompatibility
      State Tangent Charge Residue H Q C →
      Nonempty
        (UnruhDrivenChiralTubuleBoundary
          State Tangent Charge Residue H Q C)

attribute [rep_depth operator]
  HessianCollapseEvent
  ShearReadout
  ExtremeShearThreshold
  CrossesShearThreshold
  ExtremeShearThreshold.crosses_iff
  UnruhShearCalibration
  UnruhShearCalibration.driven_state_crosses_shear_threshold
  UnruhShearCalibration.unruh_temperature
  TopologicalObstruction
  TopologicalObstruction.not_flat_of_nonzero
  ChiralResidue
  ChiralTubuleBoundaryWitness
  ChiralTubuleBoundaryWitness.collapse_state_not_flat
  ChiralTubuleBoundaryWitness.collapse_state_on_chiral_lightcone
  ChiralTubuleBoundaryWitness.collapse_state_crosses_threshold
  ChiralTubuleBoundaryWitness.exists_stable_chiral_residue
  UnruhDrivenChiralTubuleBoundary
  UnruhDrivenChiralTubuleBoundary.unruh_crosses_boundary_threshold
  UnruhDrivenChiralTubuleBoundary.collapse_state_not_flat
  UnruhDrivenChiralTubuleBoundary.exists_stable_chiral_residue
  UnruhDrivenChiralTubuleBoundary.unruh_temperature
  ConservedSnapBoundary
  ConservedSnapBoundary.state_not_flat
  ConservedSnapBoundary.cannot_flow_to_flat
  ConservedSnapBoundary.no_nontrivial_flattening
  BrewsterDrazinBoundary
  BrewsterDrazinBoundary.rp_eq_zero
  BrewsterDrazinBoundary.killed_sector
  BrewsterDrazinBoundary.reflected_core_identity
  ChiralLightconeStinespringBoundary
  ChiralLightconeStinespringBoundary.accessible_loss_eq_hidden_information
  ChiralLightconeStinespringBoundary.hidden_right_of_visible_left
  ChiralLightconeStinespringBoundary.hidden_left_of_visible_right
  TomitaChiralLocalLossBoundary
  TomitaChiralLocalLossBoundary.locally_lost_global_in_commutant
  TomitaChiralLocalLossBoundary.locally_lost_has_chiral_lightcone_readout
  TomitaChiralLocalLossBoundary.locally_lost_is_commutant_chiral_lightcone
  JonesRankCollapseEvent
  JonesRankCollapseEvent.p_eigenvalue_eq_zero
  JonesRankCollapseEvent.r_p_eq_zero
  ChiralTubuleBoundaryCompatibility
  ChiralTubuleBoundaryOwnerTarget
  UnruhDrivenChiralTubuleCompatibility
  UnruhDrivenChiralTubuleOwnerTarget

end InfoGeometry.OperatorAlgebra.ChiralTubuleBoundary
