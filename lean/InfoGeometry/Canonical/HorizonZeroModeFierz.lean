import Mathlib.Tactic
import InfoGeometry.Canonical.DrazinCentralizerErlangen
import InfoGeometry.Meta.Architecture

/-!
# Horizon zero-mode Fierz socket

Publication-facing facade for the final principle:

```text
physical observables = modular zero modes living on the Drazin horizon
```

This is not a proof of the geometric holographic principle in GR.  It is the
operator-algebraic zero-mode horizon principle:

```text
A_phys(A, φ) = (p_A M p_A)^{φ_A}
```

implemented as:

* Drazin support/horizon from `DrazinSupportData`;
* modular zero mode from `IsModularZeroMode`;
* compressed centralizer from `DrazinCentralizerErlangen`;
* expectation-only Fierz readout from `DrazinFierzBridge`.

The Fierz residual law remains supplied compatibility data.
-/

noncomputable section

namespace InfoGeometry.Canonical.HorizonZeroModeFierz

open InfoGeometry.Canonical.DrazinCentralizerErlangen
open InfoGeometry.Canonical.DrazinFierzBridge
open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.OperatorAlgebra.Thermodynamics

/-! ## 1. Horizon zero-mode sanctuary -/

/--
Zero mode on the Drazin horizon:
the observable is Drazin-corner localized and modular fixed.
-/
@[rep_depth operator]
def IsHorizonZeroMode
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (x : Obs) : Prop :=
  PhysicalAlgebraCondition S x

/--
Leakage operator from a frozen Drazin horizon.
-/
@[rep_depth operator]
def leakageOperator
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (q : Obs)
    (t : ℝ) : Obs :=
  modularLeakageOperator S.flow S.horizon q t

/--
If the Drazin horizon is fixed by modular flow and `q` annihilates it, there is
no leakage.
-/
@[rep_depth operator]
theorem no_leakage_of_fixed_horizon
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (q : Obs)
    (hOrth : q * S.horizon.p = 0) :
    ∀ t : ℝ,
      leakageOperator S q t = 0 :=
  no_leakage_of_modular_invariant_boundary
    S.flow S.horizon q S.centralizer_horizon hOrth

/-- A horizon zero mode is exactly an element of the compressed centralizer. -/
@[rep_depth operator]
theorem horizon_zero_mode_iff_compressed_centralizer
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (x : Obs) :
    IsHorizonZeroMode S x ↔
      InDrazinCompressedCentralizer S.flow S.horizon x :=
  Iff.rfl

/-! ## 2. Horizon Fierz law -/

/--
Fierz channel observables are admissible when each channel of `Aᴰ` is a zero
mode on the Drazin horizon.

This is intentionally weaker than requiring `Aᴰ` itself to be fixed by modular
flow.
-/
@[rep_depth operator]
def ChannelsAreHorizonZeroModes
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (C : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs) : Prop :=
  ∀ ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel,
    IsHorizonZeroMode S (C.channel ch S.horizon.AD)

/--
Horizon zero-mode Fierz law.

The coordinates are expectation values of Drazin-stabilized channel
observables.  The channels are required to be horizon zero modes, but the raw
operator `Aᴰ` is not required to be a modular zero mode.  No Fierz quadric
identity is stored here; concrete models must prove any residual equation from
lower definitions.
-/
@[rep_depth operator]
structure HorizonZeroModeFierzLaw
    (Obs : Type*) [Ring Obs] [Star Obs] [SMul ℂ Obs] where
  sanctuary :
    DrazinCentralizerSanctuary Obs
  channels :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs
  residual :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzResidual
  channels_zero_modes :
    ChannelsAreHorizonZeroModes sanctuary channels
  coords :
    InfoGeometry.Canonical.DrazinFierzBridge.NormalizedFierzCoordinates :=
      sanctuaryExpectationFierzVector sanctuary channels
  coords_are_horizon_expectations :
    ∀ ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel,
      coords.coord ch =
        centralizerExpectationFierzCoordinate
          sanctuary.state
          channels
          sanctuary.horizon
          ch

namespace HorizonZeroModeFierzLaw

variable {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
variable (F : HorizonZeroModeFierzLaw Obs)

/-- The horizon supporting the Fierz readout is modular fixed. -/
@[rep_depth operator]
theorem horizon_fixed :
    ModularInvariantDrazinBoundary F.sanctuary.flow F.sanctuary.horizon :=
  F.sanctuary.centralizer_horizon

/-- The supplied Fierz channels are horizon zero modes. -/
@[rep_depth operator]
theorem channels_are_zero_modes :
    ChannelsAreHorizonZeroModes F.sanctuary F.channels :=
  F.channels_zero_modes

/-- Final coordinates are horizon expectation values of Drazin-stabilized channels. -/
@[rep_depth operator]
theorem coords_are_horizon_expectations_eq
    (ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel) :
    F.coords.coord ch =
      centralizerExpectationFierzCoordinate
        F.sanctuary.state
        F.channels
        F.sanctuary.horizon
        ch :=
  F.coords_are_horizon_expectations ch

end HorizonZeroModeFierzLaw

end InfoGeometry.Canonical.HorizonZeroModeFierz
