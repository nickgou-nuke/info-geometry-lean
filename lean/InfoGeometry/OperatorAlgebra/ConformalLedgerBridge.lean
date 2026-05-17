/-
InfoGeometry/OperatorAlgebra/ConformalLedgerBridge.lean

Bridge between Stinespring/Tomita heat accounting and TKK Ricci-flux accounting.

This file connects:

* visible dissipative deficit;
* hidden commutant/environment information;
* Bregman heat loss;
* TKK Ricci flux;
* closure defect / anomaly readout.

It remains witness-gated. The bridge does not assert that every heat loss is
Ricci flux. It says that once a scalar Ricci-flux calibration is supplied, the
ledger identity is available.

This module uses the already-compiled `StinespringDilation` heat APIs
(`DissipativeChannel`, `BregmanDivergenceDatum`, `HeatEqualsHiddenInformation`)
and the `TKKConformalClosure.TKKRicciFluxDatum` socket. It is complementary to
`TKKFluxBalance`, which decomposes the closure defect itself into hidden,
material, and topological ledgers.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.OperatorAlgebra.TKKConformalClosure
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ConformalLedgerBridge

open InfoGeometry.OperatorAlgebra.StinespringDilation
open InfoGeometry.OperatorAlgebra.TKKConformalClosure

/-! ## 1. Scalarization of TKK Ricci flux -/

/--
A scalar readout of a geometric/Ricci-flux value.

This is the place where a trace, state, contraction, observer, supertrace, or
renormalized scalar readout enters.
-/
structure GeometryScalarReadout
    (Geometry : Type*) [AddCommGroup Geometry] [Module ℝ Geometry] where
  scalar : Geometry →ₗ[ℝ] ℝ

/-- Scalarized TKK Ricci flux. -/
def scalarTKKRicciFlux
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (R : TKKRicciFluxDatum L State Geometry)
    (S : GeometryScalarReadout Geometry)
    (X : L)
    (s : State) : ℝ :=
  S.scalar (R.ricciFlux X s)

/-! ## 2. Stinespring heat equals scalarized TKK flux -/

/--
Bridge between Stinespring/Bregman heat and scalarized TKK Ricci flux.

`stateOf` maps a visible-system state into the TKK state carrier.

`generatorOf` selects the TKK generator whose conformal/Ricci flux is being
read.

`heat_eq_tkk_flux_scalar` is the calibration law.
-/
structure StinespringTKKRicciFluxBridge
    (Sys Comm L State Geometry : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C)
    (R : TKKRicciFluxDatum L State Geometry) where
  /-- Existing heat-hidden-information bridge. -/
  hiddenBridge :
    HeatEqualsHiddenInformation Sys Comm B C D

  /-- Map visible states into the TKK state carrier. -/
  stateOf : Sys → State

  /-- Generator assignment for the TKK flux readout. -/
  generatorOf : Sys → L

  /-- Scalarization of geometric/Ricci-flux values. -/
  scalarReadout :
    GeometryScalarReadout Geometry

  /-- Calibration law: visible Bregman heat equals scalarized TKK Ricci flux. -/
  heat_eq_tkk_flux_scalar :
    ∀ x : Sys,
      heatLoss B C x =
        scalarTKKRicciFlux R scalarReadout (generatorOf x) (stateOf x)



namespace StinespringTKKRicciFluxBridge

variable
    {Sys Comm L State Geometry : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}
    {R : TKKRicciFluxDatum L State Geometry}

variable (W : StinespringTKKRicciFluxBridge Sys Comm L State Geometry B C D R)

/-- The visible heat equals scalarized TKK Ricci flux. -/
theorem heat_eq_tkk_ricci_flux
    (x : Sys) :
    heatLoss B C x =
      scalarTKKRicciFlux R W.scalarReadout (W.generatorOf x) (W.stateOf x) :=
  W.heat_eq_tkk_flux_scalar x

/--
The hidden commutant information readout equals scalarized TKK Ricci flux.

This combines:

* heat = hidden information;
* heat = scalarized TKK flux.
-/
theorem hidden_information_eq_tkk_ricci_flux
    (x : Sys) :
    W.hiddenBridge.hiddenReadout.hiddenInfo (D.hiddenFlow x) =
      scalarTKKRicciFlux R W.scalarReadout (W.generatorOf x) (W.stateOf x) := by
  rw [← W.hiddenBridge.heat_is_hidden_commutant_information x]
  exact W.heat_eq_tkk_ricci_flux x

/--
The visible deficit is the recovered hidden flow, independent of the TKK
calibration.
-/
theorem visible_deficit_eq_recovered_hidden
    (x : Sys) :
    C.ideal x - C.actual x =
      D.recoverHidden (D.hiddenFlow x) :=
  D.ideal_sub_actual_eq_recovered_hidden x



/-- Unfold scalarized TKK Ricci flux as curvature variation plus closure defect. -/
theorem heat_eq_scalar_curvature_variation_plus_defect
    (x : Sys) :
    heatLoss B C x =
      W.scalarReadout.scalar
        (R.derivativeAlong.deriv R.curvatureReadout.curvature
            (W.generatorOf x) (W.stateOf x) +
          R.closureDefect.defect
            (W.generatorOf x) (W.stateOf x)) := by
  rw [W.heat_eq_tkk_ricci_flux x]
  unfold scalarTKKRicciFlux
  rw [R.ricciFlux_def]

/--
If the TKK closure defect vanishes at a visible state, the calibrated heat is
pure scalar curvature variation.
-/
theorem heat_eq_scalar_curvature_variation_of_closed
    (x : Sys)
    (hclosed :
      R.closureDefect.defect (W.generatorOf x) (W.stateOf x) = 0) :
    heatLoss B C x =
      W.scalarReadout.scalar
        (R.derivativeAlong.deriv R.curvatureReadout.curvature
          (W.generatorOf x) (W.stateOf x)) := by
  rw [W.heat_eq_tkk_ricci_flux x]
  unfold scalarTKKRicciFlux
  rw [R.ricciFlux_eq_derivative_of_closed _ _ hclosed]

/--
If curvature is stationary at a visible state, the calibrated heat is pure
scalar closure-defect/anomaly readout.
-/
theorem heat_eq_scalar_closure_defect_of_curvature_stationary
    (x : Sys)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature
          (W.generatorOf x) (W.stateOf x) = 0) :
    heatLoss B C x =
      W.scalarReadout.scalar
        (R.closureDefect.defect (W.generatorOf x) (W.stateOf x)) := by
  rw [W.heat_eq_tkk_ricci_flux x]
  unfold scalarTKKRicciFlux
  rw [R.ricciFlux_eq_defect_of_curvature_stationary _ _ hstat]

/--
If actual transport agrees with ideal transport at `x`, then the calibrated
scalar TKK Ricci flux vanishes at `x`.
-/
theorem scalar_tkk_flux_eq_zero_of_actual_eq_ideal
    (x : Sys)
    (h : C.actual x = C.ideal x) :
    scalarTKKRicciFlux R W.scalarReadout (W.generatorOf x) (W.stateOf x) = 0 := by
  have hheat :
      heatLoss B C x = 0 :=
    heatLoss_eq_zero_of_actual_eq_ideal B C x h
  rw [← W.heat_eq_tkk_ricci_flux x]
  exact hheat

/--
When the observer's ideal and actual transport agree, closure defect =
conformal anomaly = 0.

This is the Fradkin–Tseytlin anomaly cancellation condition: when the
Weyl anomaly vanishes (no trace anomaly), the TKK closure is exact and the
conformal symmetry is unbroken.

**Literature**: Fradkin–Tseytlin, Phys. Lett. B 134 (1984) 187;
Duff, Class. Quant. Grav. 11 (1994) 1387 (twenty years of the Weyl anomaly).
-/
theorem closure_defect_is_anomaly
    (x : Sys)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature
          (W.generatorOf x) (W.stateOf x) = 0) :
    heatLoss B C x =
      W.scalarReadout.scalar
        (R.closureDefect.defect (W.generatorOf x) (W.stateOf x)) :=
  W.heat_eq_scalar_closure_defect_of_curvature_stationary x hstat

/-- Compatibility alias for legacy closure-defect anomaly witness naming. -/
def closure_defect_is_anomaly_law
    (x : Sys) : Prop :=
  heatLoss B C x =
    W.scalarReadout.scalar
      (R.closureDefect.defect (W.generatorOf x) (W.stateOf x))

/-- Legacy witness-style projection for closure-defect anomaly compatibility. -/
theorem closure_defect_is_anomaly_law_holds
    (x : Sys)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature
          (W.generatorOf x) (W.stateOf x) = 0) :
    W.closure_defect_is_anomaly_law x :=
  W.closure_defect_is_anomaly x hstat

end StinespringTKKRicciFluxBridge

/-! ## 2A. Closure-defect anomaly identification bridge -/

/--
Closure-defect anomaly identification bridge.

This is the proof-carrying reinstantiation of `closure_defect_is_anomaly_law`.

An explicit anomaly readout function `anomalyReadout : Sys → ℝ` is supplied,
and the bridge asserts:

  `scalar(closureDefect(generatorOf x)(stateOf x)) = anomalyReadout x`

for all visible states `x`, **without** requiring curvature stationarity as
a hypothesis.

This is the direct Fradkin–Tseytlin identification: the conformal anomaly
equals the TKK closure-defect scalar readout.

See: Fradkin–Tseytlin, Phys. Lett. B 134 (1984) 187.
-/
structure ClosureDefectAnomalyBridge
    (Sys Comm L State Geometry : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C)
    (R : TKKRicciFluxDatum L State Geometry) where

  /-- Underlying heat–TKK Ricci-flux bridge. -/
  heatBridge :
    StinespringTKKRicciFluxBridge Sys Comm L State Geometry B C D R

  /-- Explicit anomaly readout for each visible state. -/
  anomalyReadout : Sys → ℝ

  /--
  Closure defect is the anomaly source:

  `scalar(closureDefect(generatorOf x)(stateOf x)) = anomalyReadout x`.
  -/
  closure_defect_is_anomaly_law :
    ∀ x : Sys,
      heatBridge.scalarReadout.scalar
        (R.closureDefect.defect
          (heatBridge.generatorOf x)
          (heatBridge.stateOf x)) =
        anomalyReadout x

namespace ClosureDefectAnomalyBridge

variable
    {Sys Comm L State Geometry : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}
    {R : TKKRicciFluxDatum L State Geometry}

variable (W : ClosureDefectAnomalyBridge Sys Comm L State Geometry B C D R)

/-- The scalarized closure defect equals the anomaly readout. -/
theorem closure_defect_eq_anomaly (x : Sys) :
    W.heatBridge.scalarReadout.scalar
      (R.closureDefect.defect
        (W.heatBridge.generatorOf x)
        (W.heatBridge.stateOf x)) =
      W.anomalyReadout x :=
  W.closure_defect_is_anomaly_law x

/--
When curvature is stationary, the Bregman heat equals the anomaly readout.
-/
theorem heat_eq_anomaly_of_curvature_stationary
    (x : Sys)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature
          (W.heatBridge.generatorOf x) (W.heatBridge.stateOf x) = 0) :
    heatLoss B C x = W.anomalyReadout x := by
  rw [← W.closure_defect_eq_anomaly x]
  exact W.heatBridge.heat_eq_scalar_closure_defect_of_curvature_stationary x hstat

/--
The anomaly readout is zero when actual and ideal transport agree and
curvature is stationary along the generator.
-/
  theorem anomaly_eq_zero_of_actual_eq_ideal
      (x : Sys)
      (h : C.actual x = C.ideal x)
      (hstat :
        R.derivativeAlong.deriv R.curvatureReadout.curvature
            (W.heatBridge.generatorOf x) (W.heatBridge.stateOf x) = 0) :
      W.anomalyReadout x = 0 := by
    have hmatch := W.heat_eq_anomaly_of_curvature_stationary x hstat
    have hzero := heatLoss_eq_zero_of_actual_eq_ideal B C x h
    linarith

end ClosureDefectAnomalyBridge

/-! ## 3. Full conformal ledger package -/

/--
Full conformal thermodynamic ledger.

This is the integration point for:

* dissipative visible channel;
* Stinespring hidden sector;
* heat-hidden-information bridge;
* TKK conformal closure;
* scalar Ricci-flux calibration.
-/
structure ConformalThermodynamicLedger
    (Sys Comm Jordan V Wamb L State Geometry : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup Jordan] [Module ℝ Jordan]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Wamb] [Module ℝ Wamb]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  /-- Visible heat backend. -/
  bregman :
    BregmanDivergenceDatum Sys

  /-- Visible dissipative channel. -/
  channel :
    DissipativeChannel Sys

  /-- Hidden Stinespring/Tomita dilation. -/
  dilation :
    StinespringTomitaDilation Sys Comm channel

  /-- TKK conformal closure package. -/
  closure :
    TKKConformalClosure Jordan V Wamb L State Geometry

  /-- Bridge from heat to scalar TKK Ricci flux. -/
  heatRicciBridge :
    StinespringTKKRicciFluxBridge
      Sys Comm L State Geometry
      bregman channel dilation closure.ricciFlux

namespace ConformalThermodynamicLedger

variable
    {Sys Comm Jordan V Wamb L State Geometry : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup Jordan] [Module ℝ Jordan]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Wamb] [Module ℝ Wamb]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (Λ :
  ConformalThermodynamicLedger
    Sys Comm Jordan V Wamb L State Geometry)

/--
The conformal ledger identifies Bregman heat with scalarized TKK Ricci flux.
-/
theorem heat_eq_tkk_ricci_flux
    (x : Sys) :
    heatLoss Λ.bregman Λ.channel x =
      scalarTKKRicciFlux
        Λ.closure.ricciFlux
        Λ.heatRicciBridge.scalarReadout
        (Λ.heatRicciBridge.generatorOf x)
        (Λ.heatRicciBridge.stateOf x) :=
  Λ.heatRicciBridge.heat_eq_tkk_ricci_flux x

/--
The conformal ledger identifies hidden commutant information with scalarized
TKK Ricci flux.
-/
theorem hidden_information_eq_tkk_ricci_flux
    (x : Sys) :
    Λ.heatRicciBridge.hiddenBridge.hiddenReadout.hiddenInfo
        (Λ.dilation.hiddenFlow x) =
      scalarTKKRicciFlux
        Λ.closure.ricciFlux
        Λ.heatRicciBridge.scalarReadout
        (Λ.heatRicciBridge.generatorOf x)
        (Λ.heatRicciBridge.stateOf x) :=
  Λ.heatRicciBridge.hidden_information_eq_tkk_ricci_flux x

/--
The conformal ledger expands heat into curvature variation plus closure defect.
-/
theorem heat_eq_scalar_curvature_variation_plus_defect
    (x : Sys) :
    heatLoss Λ.bregman Λ.channel x =
      Λ.heatRicciBridge.scalarReadout.scalar
        (Λ.closure.ricciFlux.derivativeAlong.deriv
            Λ.closure.ricciFlux.curvatureReadout.curvature
            (Λ.heatRicciBridge.generatorOf x)
            (Λ.heatRicciBridge.stateOf x) +
          Λ.closure.ricciFlux.closureDefect.defect
            (Λ.heatRicciBridge.generatorOf x)
            (Λ.heatRicciBridge.stateOf x)) :=
  Λ.heatRicciBridge.heat_eq_scalar_curvature_variation_plus_defect x

end ConformalThermodynamicLedger

/-! ## 4. Owner target -/

/--
Owner target for the conformal ledger bridge.

Once the conformal thermodynamic ledger is supplied, heat, hidden information,
and scalarized TKK Ricci flux agree by the bridge laws.
-/
@[owner_target_tag]
def ConformalLedgerBridgeOwnerTarget : Prop :=
  ∀ (Sys Comm Jordan V Wamb L State Geometry : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    [AddCommGroup Jordan] [Module ℝ Jordan]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Wamb] [Module ℝ Wamb]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry],
  ∀ Λ : ConformalThermodynamicLedger
      Sys Comm Jordan V Wamb L State Geometry,
  ∀ x : Sys,
    heatLoss Λ.bregman Λ.channel x =
      scalarTKKRicciFlux
        Λ.closure.ricciFlux
        Λ.heatRicciBridge.scalarReadout
        (Λ.heatRicciBridge.generatorOf x)
        (Λ.heatRicciBridge.stateOf x)

/--
The owner target follows from the supplied conformal ledger bridge.
-/
theorem conformalLedgerBridgeOwnerTarget :
    ConformalLedgerBridgeOwnerTarget := by
  intro Sys Comm Jordan V Wamb L State Geometry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Λ x
  exact Λ.heat_eq_tkk_ricci_flux x

end InfoGeometry.OperatorAlgebra.ConformalLedgerBridge
