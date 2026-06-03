import Mathlib
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

/-!
# Spin-Bogoliubov Frame

Dimension-agnostic bridge from a spin-connection frame selector to the
Stinespring/Tomita information ledger.

The module proves the conservation part by reusing
`StinespringTomitaDilation`: visible deficit is exactly recovered hidden flow.
The Einstein/Ricci side remains a separate proof-carrying calibration.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpinBogoliubovFrame

open InfoGeometry.OperatorAlgebra.StinespringDilation

set_option linter.dupNamespace false

/-! ## Spin connection datum -/

/--
A spin-connection-like datum controlling Bogoliubov frame choice.

`Frame` is an abstract parameter space for local spin frames, observers, or
connection values.  `omega θ` is the bounded operatorial connection readout at
frame `θ`; `curvature θ` is a scalar curvature/anomaly readout at this layer.
-/
structure SpinConnectionDatum
    (Frame Sys : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys] where
  /-- Spin connection/operator readout at a frame. -/
  omega : Frame → Sys →L[ℝ] Sys

  /-- Scalar curvature/anomaly readout. -/
  curvature : Frame → ℝ

  /-- Inertial/flat frames. -/
  inertial : Frame → Prop

  /-- In inertial frames, the curvature readout vanishes. -/
  inertial_curvature_zero :
    ∀ θ : Frame, inertial θ → curvature θ = 0

namespace SpinConnectionDatum

variable
    {Frame Sys : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]

/--
In an inertial frame, the curvature/anomaly readout vanishes.
-/
theorem curvature_eq_zero_of_inertial
    (S : SpinConnectionDatum Frame Sys)
    (θ : Frame)
    (hθ : S.inertial θ) :
    S.curvature θ = 0 :=
  S.inertial_curvature_zero θ hθ

end SpinConnectionDatum

/-! ## Spin-Bogoliubov channel family -/

/--
A spin connection calibrated as a Bogoliubov frame setter.

For each frame `θ`, the visible system has a dissipative channel and a
Stinespring/Tomita dilation into a commutant/environment carrier.  The
connection does not definitionally produce the channel; concrete
representations should add separate owner theorems for model-specific
spin/Bogoliubov calibration.
-/
structure SpinBogoliubovFrame
    (Frame Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm] where
  /-- Spin connection data. -/
  spin : SpinConnectionDatum Frame Sys

  /-- Visible channel assigned to a frame. -/
  channel : Frame → DissipativeChannel Sys

  /-- Stinespring/Tomita dilation of each visible channel. -/
  dilation :
    ∀ θ : Frame,
      StinespringTomitaDilation Sys Comm (channel θ)

  /--
  In an inertial frame, there is no visible dissipative loss:
  actual transport agrees with ideal transport.
  -/
  inertial_lossless :
    ∀ θ : Frame,
      spin.inertial θ →
        (channel θ).actual = (channel θ).ideal

namespace SpinBogoliubovFrame

variable
    {Frame Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]

variable (S : SpinBogoliubovFrame Frame Sys Comm)

/--
For each frame, the visible deficit is the recovered hidden commutant flow.
-/
theorem deficit_eq_recovered_hidden
    (θ : Frame)
    (x : Sys) :
    (S.channel θ).ideal x - (S.channel θ).actual x =
      (S.dilation θ).recoverHidden ((S.dilation θ).hiddenFlow x) :=
  (S.dilation θ).ideal_sub_actual_eq_recovered_hidden x

/--
In an inertial frame, visible heat loss vanishes for any Bregman backend.
-/
theorem heatLoss_eq_zero_of_inertial
    (B : BregmanDivergenceDatum Sys)
    (θ : Frame)
    (hθ : S.spin.inertial θ)
    (x : Sys) :
    heatLoss B (S.channel θ) x = 0 := by
  have hmap :
      (S.channel θ).actual x = (S.channel θ).ideal x := by
    have h := S.inertial_lossless θ hθ
    exact congrArg (fun L : Sys →L[ℝ] Sys => L x) h
  exact heatLoss_eq_zero_of_actual_eq_ideal B (S.channel θ) x hmap

/--
In an inertial frame, the curvature/anomaly readout vanishes.
-/
theorem curvature_eq_zero_of_inertial
    (θ : Frame)
    (hθ : S.spin.inertial θ) :
    S.spin.curvature θ = 0 :=
  S.spin.inertial_curvature_zero θ hθ

end SpinBogoliubovFrame

/-! ## Heat and hidden-information calibration -/

/--
A spin-frame heat calibration.

For every frame `θ`, visible Bregman heat is calibrated as hidden-sector
information through the Stinespring/Tomita dilation.
-/
structure SpinHeatCalibration
    (Frame Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (S : SpinBogoliubovFrame Frame Sys Comm) where
  /-- Bregman divergence backend. -/
  bregman : BregmanDivergenceDatum Sys

  /-- Heat-hidden-information bridge for each frame. -/
  heatBridge :
    ∀ θ : Frame,
      HeatEqualsHiddenInformation
        Sys Comm bregman (S.channel θ) (S.dilation θ)

namespace SpinHeatCalibration

variable
    {Frame Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {S : SpinBogoliubovFrame Frame Sys Comm}

variable (C : SpinHeatCalibration Frame Sys Comm S)

/--
Visible heat equals hidden commutant information in each frame.
-/
theorem heat_eq_hidden_information
    (θ : Frame)
    (x : Sys) :
    heatLoss C.bregman (S.channel θ) x =
      (C.heatBridge θ).hiddenReadout.hiddenInfo
        ((S.dilation θ).hiddenFlow x) :=
  (C.heatBridge θ).heat_is_hidden_commutant_information x

/--
The calibrated heat readout is nonnegative.
-/
theorem heat_nonneg
    (θ : Frame)
    (x : Sys) :
    0 ≤ heatLoss C.bregman (S.channel θ) x :=
  heatLoss_nonneg C.bregman (S.channel θ) x

/--
In inertial frames, calibrated heat vanishes.
-/
theorem heat_eq_zero_of_inertial
    (θ : Frame)
    (hθ : S.spin.inertial θ)
    (x : Sys) :
    heatLoss C.bregman (S.channel θ) x = 0 :=
  S.heatLoss_eq_zero_of_inertial C.bregman θ hθ x

end SpinHeatCalibration

/-! ## Curvature / Einstein readout carrier -/

/--
A curvature/stress readout calibrated to a spin-Bogoliubov channel family.

This is the future bridge toward Ricci flux or Einstein-type equations.
Stinespring conservation does not itself imply a field equation.
-/
structure SpinEinsteinReadoutCalibration
    (Frame Sys Comm Curv Stress : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (S : SpinBogoliubovFrame Frame Sys Comm) where
  /-- Curvature/Ricci/Einstein-side readout. -/
  curvatureReadout : Frame → Curv

  /-- Stress/energy/heat-side readout. -/
  stressReadout : Frame → Stress

namespace SpinEinsteinReadoutCalibration

variable
    {Frame Sys Comm Curv Stress : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {S : SpinBogoliubovFrame Frame Sys Comm}

variable (E : SpinEinsteinReadoutCalibration Frame Sys Comm Curv Stress S)

end SpinEinsteinReadoutCalibration

/-! ## Owner targets -/

/--
Owner target for spin-Bogoliubov conservation.

Once a spin-Bogoliubov frame is supplied, visible deficit is exactly recovered
hidden flow in every frame.
-/
@[owner_target_tag]
def SpinBogoliubovConservationOwnerTarget : Prop :=
  ∀ (Frame Sys Comm : Type*),
  ∀ [NormedAddCommGroup Sys], ∀ [NormedSpace ℝ Sys],
  ∀ [NormedAddCommGroup Comm], ∀ [NormedSpace ℝ Comm],
  ∀ S : SpinBogoliubovFrame Frame Sys Comm,
  ∀ θ : Frame,
  ∀ x : Sys,
    (S.channel θ).ideal x - (S.channel θ).actual x =
      (S.dilation θ).recoverHidden ((S.dilation θ).hiddenFlow x)

/--
The spin-Bogoliubov conservation target follows from Stinespring/Tomita
dilation.
-/
theorem spinBogoliubovConservationOwnerTarget :
    SpinBogoliubovConservationOwnerTarget := by
  intro Frame Sys Comm _ _ _ _ S θ x
  exact S.deficit_eq_recovered_hidden θ x

/--
Owner target for calibrated heat as hidden information.
-/
@[owner_target_tag]
def SpinHeatHiddenInformationOwnerTarget : Prop :=
  ∀ (Frame Sys Comm : Type*),
  ∀ [NormedAddCommGroup Sys], ∀ [NormedSpace ℝ Sys],
  ∀ [NormedAddCommGroup Comm], ∀ [NormedSpace ℝ Comm],
  ∀ S : SpinBogoliubovFrame Frame Sys Comm,
  ∀ C : SpinHeatCalibration Frame Sys Comm S,
  ∀ θ : Frame,
  ∀ x : Sys,
    heatLoss C.bregman (S.channel θ) x =
      (C.heatBridge θ).hiddenReadout.hiddenInfo
        ((S.dilation θ).hiddenFlow x)

/--
The calibrated heat-hidden-information target follows from the supplied bridge.
-/
theorem spinHeatHiddenInformationOwnerTarget :
    SpinHeatHiddenInformationOwnerTarget := by
  intro Frame Sys Comm _ _ _ _ S C θ x
  exact C.heat_eq_hidden_information θ x

attribute [rep_depth operator]
  SpinConnectionDatum
  SpinConnectionDatum.curvature_eq_zero_of_inertial
  SpinBogoliubovFrame
  SpinBogoliubovFrame.deficit_eq_recovered_hidden
  SpinBogoliubovFrame.heatLoss_eq_zero_of_inertial
  SpinBogoliubovFrame.curvature_eq_zero_of_inertial
  SpinHeatCalibration
  SpinHeatCalibration.heat_eq_hidden_information
  SpinHeatCalibration.heat_nonneg
  SpinHeatCalibration.heat_eq_zero_of_inertial
  SpinEinsteinReadoutCalibration
  SpinBogoliubovConservationOwnerTarget
  spinBogoliubovConservationOwnerTarget
  SpinHeatHiddenInformationOwnerTarget
  spinHeatHiddenInformationOwnerTarget

end InfoGeometry.OperatorAlgebra.SpinBogoliubovFrame
