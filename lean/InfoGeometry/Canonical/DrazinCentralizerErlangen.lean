import Mathlib.Tactic
import InfoGeometry.Canonical.DrazinFierzBridge
import InfoGeometry.Canonical.DrazinModularPersistence
import InfoGeometry.Meta.Architecture

/-!
# Drazin centralizer Erlangen socket

Final theorem-safe socket:

```text
Drazin stabilization
  -> modular centralizer horizon
  -> no leakage
  -> expectation-only Fierz readout
  -> model-supplied residual law
```

The principle is:

```text
Drazin cuts; modular flow transports; the centralizer anchors; the state measures.
```

This file does not introduce a competing modular-flow API.  It uses the repo
`DrazinModularPersistence.ModularFlow` owner through
`InfoGeometry.OperatorAlgebra.Thermodynamics.ModularFlow`.

It also does not claim that arbitrary observables satisfy Fierz identities.
Residual vanishing is kept as an explicit law of the supplied socket.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinCentralizerErlangen

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.OperatorAlgebra.Thermodynamics

/-! ## 1. Drazin-compressed centralizer predicates -/

/--
Publication-safe Drazin centralizer sanctuary.

`horizon` already carries the projection-level facts used in this file:
`p = A * AD`, Drazin laws, and `star p = p`.  The compressed weight is not an
extra arbitrary proposition: it is the concrete state readout `φ(p)` exposed by
`compressedWeight` below.
-/
@[rep_depth operator]
structure DrazinCentralizerSanctuary
    (Obs : Type*)
    [Ring Obs]
    [Star Obs]
  [SMul ℂ Obs] where
  state :
    InfoGeometry.Canonical.DrazinFierzBridge.ExpectationState Obs
  flow :
    ModularFlow Obs
  horizon :
    DrazinSupportData Obs
  centralizer_horizon :
    ModularInvariantDrazinBoundary flow horizon

/--
Membership in the algebraic Drazin corner `p M p`, stated as a predicate.

If `p` is a self-adjoint projection this is the usual von Neumann corner.
For a merely algebraic idempotent this remains a theorem-safe compression
predicate.
-/
@[rep_depth operator]
def InDrazinCorner
    {Obs : Type*} [Ring Obs] [Star Obs]
    (D : DrazinSupportData Obs)
    (x : Obs) : Prop :=
  D.p * x * D.p = x

/--
Membership in the Drazin-compressed centralizer:
the observable is in the Drazin corner and fixed by modular flow.
-/
@[rep_depth operator]
def InDrazinCompressedCentralizer
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (x : Obs) : Prop :=
  InDrazinCorner D x ∧ IsModularZeroMode flow x

/--
Physical algebra condition:
membership in the Drazin-compressed modular centralizer.
-/
@[rep_depth operator]
def PhysicalAlgebraCondition
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (x : Obs) : Prop :=
  InDrazinCompressedCentralizer S.flow S.horizon x

namespace DrazinCentralizerSanctuary

variable {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
variable (S : DrazinCentralizerSanctuary Obs)

/-- The compressed horizon weight is the expectation of the Drazin support. -/
@[rep_depth operator]
def compressedWeight : ℂ :=
  S.state.expect S.horizon.p

/-- The sanctuary horizon is modular fixed. -/
@[rep_depth operator]
theorem horizon_modular_fixed :
    ModularInvariantDrazinBoundary S.flow S.horizon :=
  S.centralizer_horizon

/-- The sanctuary horizon support is self-adjoint. -/
@[rep_depth operator]
theorem horizon_self_adjoint :
    star S.horizon.p = S.horizon.p :=
  S.horizon.p_self_adjoint

/-- The sanctuary horizon support is idempotent. -/
@[rep_depth operator]
theorem horizon_idempotent :
    S.horizon.p * S.horizon.p = S.horizon.p :=
  DrazinSupportData.p_idempotent S.horizon

/-- Readback for the concrete compressed horizon weight. -/
@[rep_depth operator]
theorem compressedWeight_eq :
    S.compressedWeight = S.state.expect S.horizon.p :=
  rfl

end DrazinCentralizerSanctuary

/--
The Drazin horizon itself is in the compressed centralizer when it is a modular
fixed horizon.
-/
@[rep_depth operator]
theorem horizon_mem_compressed_centralizer
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (hHorizon : IsPhysicalHorizon flow D) :
    InDrazinCompressedCentralizer flow D D.p := by
  constructor
  · have hp : D.p * D.p = D.p :=
      DrazinSupportData.p_idempotent D
    calc
      D.p * D.p * D.p = D.p * (D.p * D.p) := by
        rw [mul_assoc]
      _ = D.p * D.p := by
        exact congrArg (fun y => D.p * y) hp
      _ = D.p := by
        exact hp
  · exact hHorizon

/--
If an element is in the compressed centralizer, it is a horizon zero mode.
-/
@[rep_depth operator]
theorem compressed_centralizer_is_horizon_zero_mode
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (x : Obs)
    (hx : InDrazinCompressedCentralizer flow D x) :
    IsHorizonZeroMode flow D x :=
  hx

/-! ## 2. Expectation-only Fierz readout over a centralizer horizon -/

/--
Drazin-filtered observable induced by the Drazin inverse in a horizon packet.
-/
@[rep_depth operator]
def drazinFilteredObservable
    {Obs : Type*}
    [Ring Obs]
    [Star Obs]
    (D : DrazinSupportData Obs) :
    InfoGeometry.Canonical.DrazinFierzBridge.DrazinFilteredObservable Obs :=
  D.AD

/--
Expectation-only Fierz coordinate of a Drazin horizon packet.
-/
@[rep_depth operator]
def centralizerExpectationFierzCoordinate
    {Obs : Type*}
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs]
    (φ : InfoGeometry.Canonical.DrazinFierzBridge.ExpectationState Obs)
    (C : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs)
    (D : DrazinSupportData Obs)
    (ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel) : ℂ :=
  InfoGeometry.Canonical.DrazinFierzBridge.expectationChannelFierzCoordinate φ C (drazinFilteredObservable D) ch

/--
Expectation-only Fierz vector of a Drazin horizon packet.
-/
@[rep_depth operator]
def centralizerExpectationFierzVector
    {Obs : Type*}
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs]
    (φ : InfoGeometry.Canonical.DrazinFierzBridge.ExpectationState Obs)
    (C : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs)
    (D : DrazinSupportData Obs) :
    InfoGeometry.Canonical.DrazinFierzBridge.NormalizedFierzCoordinates :=
  fun ch => centralizerExpectationFierzCoordinate φ C D ch

/--
Expectation-only Fierz vector attached to a centralizer sanctuary.
-/
@[rep_depth operator]
def sanctuaryExpectationFierzVector
    {Obs : Type*}
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (C : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs) :
    InfoGeometry.Canonical.DrazinFierzBridge.NormalizedFierzCoordinates :=
  centralizerExpectationFierzVector S.state C S.horizon

/-! ## 2A. State-relative Witten balance socket -/

/--
State-relative boson/fermion balance.

This is the Type-III-safe replacement for a global supertrace.  It is an
expectation difference in the compressed/state-relative setting.
-/
@[rep_depth operator]
structure StateRelativeWittenBalance
    (Obs : Type*)
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs] where
  sanctuary :
    DrazinCentralizerSanctuary Obs
  pEven :
    Obs
  pOdd :
    Obs
  pEven_in_phys :
    PhysicalAlgebraCondition sanctuary pEven
  pOdd_in_phys :
    PhysicalAlgebraCondition sanctuary pOdd

/-- State-relative Witten index: `φ_A(p_even) - φ_A(p_odd)`. -/
@[rep_depth operator]
def stateRelativeWittenIndex
    {Obs : Type*}
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs]
    (W : StateRelativeWittenBalance Obs) : ℂ :=
  W.sanctuary.state.expect W.pEven - W.sanctuary.state.expect W.pOdd

/-- State-relative Witten balance condition. -/
@[rep_depth operator]
def IsStateRelativeWittenBalanced
    {Obs : Type*}
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs]
    (W : StateRelativeWittenBalance Obs) : Prop :=
  stateRelativeWittenIndex W = 0

/-! ## 3. Final centralizer Erlangen socket -/

/--
Final expectation-only Drazin/Fierz centralizer law.

The field `residual_vanishes` is explicitly supplied.  This prevents
laundering a Fierz identity through the centralizer property alone.
-/
@[rep_depth operator]
structure DrazinCentralizerFierzLaw
    (Obs : Type*)
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs] where
  state :
    InfoGeometry.Canonical.DrazinFierzBridge.ExpectationState Obs
  flow :
    ModularFlow Obs
  channels :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs
  residual :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzResidual
  horizon :
    DrazinSupportData Obs
  centralizer_horizon :
    ModularInvariantDrazinBoundary flow horizon
  coords :
    InfoGeometry.Canonical.DrazinFierzBridge.NormalizedFierzCoordinates :=
      centralizerExpectationFierzVector state channels horizon
  coords_eq_expectation :
    ∀ ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel,
      coords.coord ch =
        centralizerExpectationFierzCoordinate state channels horizon ch
  residual_vanishes :
    residual.residual coords = 0

namespace DrazinCentralizerFierzLaw

variable {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
variable (K : DrazinCentralizerFierzLaw Obs)

/-- The supplied horizon is modular fixed. -/
@[rep_depth operator]
theorem horizon_is_modular_fixed :
    ModularInvariantDrazinBoundary K.flow K.horizon :=
  K.centralizer_horizon

/-- No leakage from the supplied centralizer horizon into an annihilating complement. -/
@[rep_depth operator]
theorem no_leakage
    (q : Obs)
    (hOrth : q * K.horizon.p = 0) :
    ∀ t : ℝ,
      modularLeakageOperator K.flow K.horizon q t = 0 :=
  no_leakage_of_modular_invariant_boundary
    K.flow K.horizon q K.centralizer_horizon hOrth

/-- The coordinate packet is the expectation-only Drazin/Fierz vector. -/
@[rep_depth operator]
theorem coords_are_expectation_readout
    (ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel) :
    K.coords.coord ch =
      centralizerExpectationFierzCoordinate K.state K.channels K.horizon ch :=
  K.coords_eq_expectation ch

/-- The final Fierz residual law is the supplied model law. -/
@[rep_depth operator]
theorem residual_eq_zero :
    K.residual.residual K.coords = 0 :=
  K.residual_vanishes

end DrazinCentralizerFierzLaw

/-! ## 4. Publication-facing final law wrapper -/

/--
Publication-facing final Drazin/Fierz law.

The sanctuary supplies:
* self-adjoint Drazin support through `DrazinSupportData`;
* modular fixedness of the horizon;
* finite compressed state/weight data.

The Fierz residual law remains explicit compatibility data.
-/
@[rep_depth operator]
structure FinalDrazinFierzLaw
    (Obs : Type*)
    [Ring Obs]
    [Star Obs]
    [SMul ℂ Obs] where
  sanctuary :
    DrazinCentralizerSanctuary Obs
  channels :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzChannelMap Obs
  residual :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzResidual
  coords :
    InfoGeometry.Canonical.DrazinFierzBridge.NormalizedFierzCoordinates :=
      sanctuaryExpectationFierzVector sanctuary channels
  coords_are_expectations :
    ∀ ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel,
      coords.coord ch =
        centralizerExpectationFierzCoordinate
          sanctuary.state
          channels
          sanctuary.horizon
          ch
  residual_vanishes :
    residual.residual coords = 0

namespace FinalDrazinFierzLaw

variable {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
variable (F : FinalDrazinFierzLaw Obs)

/-- Final readout coordinates are expectation values, not traces. -/
@[rep_depth operator]
theorem coords_eq_expectation
    (ch : InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel) :
    F.coords.coord ch =
      centralizerExpectationFierzCoordinate
        F.sanctuary.state
        F.channels
        F.sanctuary.horizon
        ch :=
  F.coords_are_expectations ch

/-- Final residual-zero law supplied by the model. -/
@[rep_depth operator]
theorem residual_eq_zero :
    F.residual.residual F.coords = 0 :=
  F.residual_vanishes

/-- The final law includes an explicit modular-fixed Drazin horizon. -/
@[rep_depth operator]
theorem horizon_modular_fixed :
    ModularInvariantDrazinBoundary F.sanctuary.flow F.sanctuary.horizon :=
  F.sanctuary.centralizer_horizon

end FinalDrazinFierzLaw

end InfoGeometry.Canonical.DrazinCentralizerErlangen
