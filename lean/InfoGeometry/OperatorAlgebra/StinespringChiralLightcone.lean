/-
InfoGeometry/OperatorAlgebra/StinespringChiralLightcone.lean

Stinespring/Tomita clinch on the chiral lightcone.

Apparent absorption/loss from the visible chiral lightcone is represented as
hidden flow into a commutant/environment sector, once a dilation witness and
lightcone calibration are supplied.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
import InfoGeometry.OperatorAlgebra.StinespringDilation

noncomputable section

namespace StinespringChiralLightcone

open InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
open InfoGeometry.OperatorAlgebra.StinespringDilation

/-! ## 1. Chiral-lightcone Stinespring stage -/

/--
A Stinespring dilation calibrated to a chiral lightcone stage.

`visibleCone` records the visible causal/lightlike sector.

`hiddenCone` records the commutant/environment lightcone sector.

The bridge says that visible loss is routed into the hidden cone.
-/
structure ChiralLightconeStinespringBridge
    (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where

  /-- Visible chiral lightcone sector. -/
  visibleCone : Set Sys

  /-- Hidden/commutant chiral lightcone sector. -/
  hiddenCone : Set Comm

  /-- Visible states on the cone leak into the hidden cone under the dilation. -/
  hiddenFlow_lands_in_hiddenCone :
    ∀ x : Sys,
      x ∈ visibleCone →
        D.hiddenFlow x ∈ hiddenCone

namespace ChiralLightconeStinespringBridge

variable
    {Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

/--
Visible lightcone loss is exactly recovered hidden/commutant flow.
-/
theorem visible_deficit_eq_hidden_flow
    (_B : ChiralLightconeStinespringBridge Sys Comm C D)
    (x : Sys) :
    C.ideal x - C.actual x =
      D.recoverHidden (D.hiddenFlow x) :=
  D.ideal_sub_actual_eq_recovered_hidden x

/--
If a visible state lies on the visible chiral cone, its hidden flow lies in the
hidden/commutant chiral cone.
-/
theorem hiddenFlow_mem_hiddenCone
    (B : ChiralLightconeStinespringBridge Sys Comm C D)
    {x : Sys}
    (hx : x ∈ B.visibleCone) :
    D.hiddenFlow x ∈ B.hiddenCone :=
  B.hiddenFlow_lands_in_hiddenCone x hx

end ChiralLightconeStinespringBridge

/-! ## 2. Heat as hidden lightcone information -/

/--
A chiral-lightcone heat/readout bridge.

This specializes the general heat-hidden-information statement to the
lightcone-calibrated Stinespring stage.
-/
structure ChiralLightconeHeatBridge
    (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (Breg : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C)
    (L : ChiralLightconeStinespringBridge Sys Comm C D) where

  hiddenReadout : HiddenInformationReadout Comm

  heat_eq_hidden_lightcone_info :
    ∀ x : Sys,
      heatLoss Breg C x =
        hiddenReadout.hiddenInfo (D.hiddenFlow x)

namespace ChiralLightconeHeatBridge

variable
    {Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {Breg : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}
    {L : ChiralLightconeStinespringBridge Sys Comm C D}

/--
Heat is hidden chiral-lightcone information once the bridge datum is supplied.
-/
theorem heat_is_hidden_lightcone_information
    (H : ChiralLightconeHeatBridge Sys Comm Breg C D L)
    (x : Sys) :
    heatLoss Breg C x =
      H.hiddenReadout.hiddenInfo (D.hiddenFlow x) :=
  H.heat_eq_hidden_lightcone_info x

end ChiralLightconeHeatBridge

end StinespringChiralLightcone
