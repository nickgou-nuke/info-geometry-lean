/-
InfoGeometry/OperatorAlgebra/StinespringDilation.lean

Stinespring-style dilation and hidden distinguishability.

This module formalizes the operator-information slogan:

  observed loss = transfer of distinguishability into an inaccessible
  environment / commutant sector.

The equality between thermodynamic heat and hidden information is not asserted
globally. It is carried by an explicit bridge datum.

This file is intentionally algebraic. Concrete quantum modules may later
strengthen the channel to a completely positive map, a trace-preserving map,
a normal map on a von Neumann algebra, or a type III modular reduction.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.StinespringDilation

set_option linter.dupNamespace false

/-! ## 1. Bregman divergence backend -/

/--
A Bregman divergence backend on a real state module.

`div ideal actual` measures the directed information/thermodynamic shear between
an ideal reference state and an actual observed state.
-/
structure BregmanBackend
    (State : Type*) [AddCommGroup State] [Module ℝ State] where
  div : State → State → ℝ

  nonneg :
    ∀ x y : State, 0 ≤ div x y

  self_eq_zero :
    ∀ x : State, div x x = 0

/-! ## 2. Open-system channel -/

/--
An open-system channel with an actual observed branch and an ideal reference
branch.

For a metal mirror, `actual` is the lossy reflected branch and `ideal` is the
lossless/unitary reference reflection.
-/
structure OpenSystemChannel
    (State : Type*) [AddCommGroup State] [Module ℝ State] where
  /-- Observed open-system branch. -/
  actual : State →ₗ[ℝ] State

  /-- Ideal closed/lossless reference branch. -/
  ideal : State →ₗ[ℝ] State

  /-- Domain on which the channel/readouts are intended to apply. -/
  regularDomain : Set State

  actual_preserves_regular :
    ∀ x : State, x ∈ regularDomain → actual x ∈ regularDomain

  ideal_preserves_regular :
    ∀ x : State, x ∈ regularDomain → ideal x ∈ regularDomain

/-! ## 3. Stinespring/Tomita dilation datum -/

/--
A Stinespring/Tomita-style dilation.

`Joint` is the enlarged system + environment carrier.

`Env` is the hidden environment/commutant carrier.

The key law is:

`ideal x = actual x + mirrorLeak(hiddenLeak x)`.

Thus the observed deficit between ideal and actual flow is represented as a
mirrored leak from the hidden sector.
-/
structure StinespringDilation
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : OpenSystemChannel State) where

  /-- Embed observed system states into the enlarged carrier. -/
  embedSystem : State →ₗ[ℝ] Joint

  /-- Closed evolution on the enlarged carrier. -/
  jointEvolution : Joint →ₗ[ℝ] Joint

  /-- Reduction back to the observed system branch. -/
  reduceSystem : Joint →ₗ[ℝ] State

  /-- Hidden/environment readout from the enlarged carrier. -/
  hiddenLeak : Joint →ₗ[ℝ] Env

  /-- Mirror/environment contribution back into system-comparison units. -/
  mirrorLeak : Env →ₗ[ℝ] State

  /-- Actual observed channel is the reduced joint evolution. -/
  actual_eq_reduced :
    ∀ x : State,
      C.actual x =
        reduceSystem (jointEvolution (embedSystem x))

  /--
  Conservation of distinguishability/accounting:

  the ideal reference state decomposes into the actual observed branch plus the
  mirrored hidden/environment contribution.
  -/
  conservation_law :
    ∀ x : State,
      C.ideal x =
        C.actual x +
          mirrorLeak (hiddenLeak (jointEvolution (embedSystem x)))

namespace StinespringDilation

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}

variable (D : StinespringDilation State Env Joint C)

/-- Hidden environment leak after joint evolution. -/
def hiddenComponent
    (x : State) : Env :=
  D.hiddenLeak (D.jointEvolution (D.embedSystem x))

/-- Mirrored hidden contribution in system units. -/
def mirroredHiddenComponent
    (x : State) : State :=
  D.mirrorLeak (D.hiddenComponent x)

/--
The ideal-minus-actual deficit is exactly the mirrored hidden component.
-/
theorem ideal_sub_actual_eq_mirroredHidden
    (x : State) :
    C.ideal x - C.actual x = D.mirroredHiddenComponent x := by
  have h := D.conservation_law x
  dsimp [mirroredHiddenComponent, hiddenComponent]
  rw [h]
  abel

/--
If the mirrored hidden component vanishes, actual and ideal branches agree.
-/
theorem actual_eq_ideal_of_zero_mirroredHidden
    {x : State}
    (hzero : D.mirroredHiddenComponent x = 0) :
    C.actual x = C.ideal x := by
  have h := D.conservation_law x
  dsimp [mirroredHiddenComponent, hiddenComponent] at hzero
  rw [hzero, add_zero] at h
  exact h.symm

end StinespringDilation

/-! ## 4. Heat loss as Bregman distinguishability deficit -/

/--
Bregman heat/information loss:

`Heat(x) = DΦ(ideal x, actual x)`.
-/
def bregmanHeatLoss
    {State : Type*} [AddCommGroup State] [Module ℝ State]
    (B : BregmanBackend State)
    (C : OpenSystemChannel State)
    (x : State) : ℝ :=
  B.div (C.ideal x) (C.actual x)

/--
Bregman heat loss is nonnegative.
-/
theorem bregmanHeatLoss_nonneg
    {State : Type*} [AddCommGroup State] [Module ℝ State]
    (B : BregmanBackend State)
    (C : OpenSystemChannel State)
    (x : State) :
    0 ≤ bregmanHeatLoss B C x :=
  B.nonneg _ _

/--
If actual and ideal branches agree at `x`, the heat loss vanishes.
-/
theorem bregmanHeatLoss_eq_zero_of_actual_eq_ideal
    {State : Type*} [AddCommGroup State] [Module ℝ State]
    (B : BregmanBackend State)
    (C : OpenSystemChannel State)
    (x : State)
    (h : C.actual x = C.ideal x) :
    bregmanHeatLoss B C x = 0 := by
  dsimp [bregmanHeatLoss]
  rw [h]
  exact B.self_eq_zero _

/--
If the hidden mirrored leak vanishes, the Bregman heat loss vanishes.
-/
theorem bregmanHeatLoss_eq_zero_of_zero_hiddenLeak
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (B : BregmanBackend State)
    {C : OpenSystemChannel State}
    (D : StinespringDilation State Env Joint C)
    (x : State)
    (hzero : D.mirroredHiddenComponent x = 0) :
    bregmanHeatLoss B C x = 0 :=
  bregmanHeatLoss_eq_zero_of_actual_eq_ideal
    B C x
    (D.actual_eq_ideal_of_zero_mirroredHidden hzero)

/-! ## 5. Hidden information readout -/

/--
A hidden-information readout on the environment/commutant carrier.
-/
structure HiddenInformationReadout
    (Env : Type*) where
  hiddenInfo : Env → ℝ

  nonneg :
    ∀ e : Env, 0 ≤ hiddenInfo e

/--
Hidden information associated to a system state through a dilation.
-/
def hiddenInformation
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}
    (D : StinespringDilation State Env Joint C)
    (I : HiddenInformationReadout Env)
    (x : State) : ℝ :=
  I.hiddenInfo (D.hiddenComponent x)

/--
Hidden information is nonnegative.
-/
theorem hiddenInformation_nonneg
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}
    (D : StinespringDilation State Env Joint C)
    (I : HiddenInformationReadout Env)
    (x : State) :
    0 ≤ hiddenInformation D I x :=
  I.nonneg _

/-! ## 6. Heat-hidden-information bridge -/

/--
Bridge saying that Bregman heat loss equals hidden environment/commutant
information.

This is the formal version of the slogan:

  heat = information hidden from the observed system.

It is a calibration datum, not an unconditional theorem of Stinespring dilation.
-/
structure HeatHiddenInformationBridge
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (B : BregmanBackend State)
    (C : OpenSystemChannel State)
    (D : StinespringDilation State Env Joint C)
    (I : HiddenInformationReadout Env) where

  /-- Heat-hidden-information equality. -/
  heat_eq_hidden :
    ∀ x : State,
      bregmanHeatLoss B C x =
        hiddenInformation D I x

namespace HeatHiddenInformationBridge

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {B : BregmanBackend State}
    {C : OpenSystemChannel State}
    {D : StinespringDilation State Env Joint C}
    {I : HiddenInformationReadout Env}

/--
Heat equals hidden information once the bridge is supplied.
-/
theorem heat_is_hidden_information
    (H : HeatHiddenInformationBridge State Env Joint B C D I)
    (x : State) :
    bregmanHeatLoss B C x =
      hiddenInformation D I x :=
  H.heat_eq_hidden x

/--
The hidden-information readout is nonnegative, hence so is heat.
-/
theorem heat_nonneg_from_hidden
    (H : HeatHiddenInformationBridge State Env Joint B C D I)
    (x : State) :
    0 ≤ bregmanHeatLoss B C x := by
  rw [heat_is_hidden_information H x]
  exact hiddenInformation_nonneg D I x

end HeatHiddenInformationBridge

/-! ## 7. Metal mirror specialization socket -/

/--
A metal mirror is an open-system optical channel equipped with a dilation and a
hidden-information thermodynamic readout.
-/
structure MetalMirrorStinespringModel
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint] where

  bregman :
    BregmanBackend State

  channel :
    OpenSystemChannel State

  dilation :
    StinespringDilation State Env Joint channel

  hiddenReadout :
    HiddenInformationReadout Env

  bridge :
    HeatHiddenInformationBridge
      State Env Joint bregman channel dilation hiddenReadout

namespace MetalMirrorStinespringModel

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]

variable (M : MetalMirrorStinespringModel State Env Joint)

/-- Heat loss of the metal mirror at a state. -/
def heat
    (x : State) : ℝ :=
  bregmanHeatLoss M.bregman M.channel x

/-- Hidden information of the metal mirror at a state. -/
def hidden
    (x : State) : ℝ :=
  hiddenInformation M.dilation M.hiddenReadout x

/--
In a calibrated metal-mirror Stinespring model, heat is hidden information.
-/
theorem heat_eq_hidden
    (x : State) :
    M.heat x = M.hidden x :=
  HeatHiddenInformationBridge.heat_is_hidden_information M.bridge x

/--
Metal-mirror heat is nonnegative.
-/
theorem heat_nonneg
    (x : State) :
    0 ≤ M.heat x := by
  rw [M.heat_eq_hidden x]
  exact hiddenInformation_nonneg M.dilation M.hiddenReadout x

end MetalMirrorStinespringModel

/-! ## 8. Lean dissipative-channel socket -/

/--
A dissipative visible-system channel together with an ideal lossless reference.

`actual` is the observed dissipative channel.

`ideal` is the reference channel that would occur without leakage into the
environment/commutant.
-/
structure DissipativeChannel
    (Sys : Type*) [NormedAddCommGroup Sys] [NormedSpace ℝ Sys] where
  actual : Sys →L[ℝ] Sys
  ideal : Sys →L[ℝ] Sys

/-! ## 9. Stinespring/Tomita dilation witness -/

/--
Stinespring/Tomita dilation of a dissipative channel.

`hiddenFlow` records the information routed into the environment/commutant.

`recoverHidden` maps the hidden sector back into the visible-system carrier
only for the purpose of the conservation identity.

The conservation law says:

`ideal x = actual x + recoverHidden (hiddenFlow x)`.

Thus the apparent dissipative deficit is not erased; it is represented by the
hidden sector.
-/
structure StinespringTomitaDilation
    (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (C : DissipativeChannel Sys) where

  /-- Hidden/environment/commutant flow. -/
  hiddenFlow : Sys →L[ℝ] Comm

  /-- Visible reconstruction of the hidden deficit. -/
  recoverHidden : Comm →L[ℝ] Sys

  /--
  Conservation of the ideal information ledger.
  -/
  conservation_law :
    ∀ x : Sys,
      C.ideal x = C.actual x + recoverHidden (hiddenFlow x)

namespace StinespringTomitaDilation

variable
    {Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {C : DissipativeChannel Sys}

/--
The visible dissipative deficit is exactly the recovered hidden flow.
-/
theorem ideal_sub_actual_eq_recovered_hidden
    (D : StinespringTomitaDilation Sys Comm C)
    (x : Sys) :
    C.ideal x - C.actual x =
      D.recoverHidden (D.hiddenFlow x) := by
  have h := D.conservation_law x
  rw [h]
  abel

/--
If no hidden information is routed out of the visible sector at `x`, then the
actual channel agrees with the ideal channel at `x`.
-/
theorem actual_eq_ideal_of_hidden_zero
    (D : StinespringTomitaDilation Sys Comm C)
    (x : Sys)
    (hzero : D.recoverHidden (D.hiddenFlow x) = 0) :
    C.actual x = C.ideal x := by
  have h := D.conservation_law x
  rw [hzero, add_zero] at h
  exact h.symm

end StinespringTomitaDilation

/-! ## 10. Bregman heat-loss backend -/

/--
A Bregman divergence backend on visible-system states.

`div ideal actual` measures the thermodynamic shear between ideal and actual
transport.
-/
structure BregmanDivergenceDatum
    (Sys : Type*) where
  div : Sys → Sys → ℝ

  nonneg :
    ∀ x y : Sys, 0 ≤ div x y

  self_eq_zero :
    ∀ x : Sys, div x x = 0

/--
Macroscopic heat loss as Bregman shear:

`Heat(x) = DΦ(ideal x, actual x)`.
-/
def heatLoss
    {Sys : Type*} [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (x : Sys) : ℝ :=
  B.div (C.ideal x) (C.actual x)

/--
Heat loss is nonnegative.
-/
theorem heatLoss_nonneg
    {Sys : Type*} [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (x : Sys) :
    0 ≤ heatLoss B C x :=
  B.nonneg _ _

/--
If actual and ideal transport agree at `x`, heat loss vanishes at `x`.
-/
theorem heatLoss_eq_zero_of_actual_eq_ideal
    {Sys : Type*} [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (x : Sys)
    (h : C.actual x = C.ideal x) :
    heatLoss B C x = 0 := by
  unfold heatLoss
  rw [h]
  exact B.self_eq_zero _

/--
If the recovered hidden deficit vanishes, then the Bregman heat loss vanishes.
-/
theorem heatLoss_eq_zero_of_hidden_zero
    {Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    {C : DissipativeChannel Sys}
    (D : StinespringTomitaDilation Sys Comm C)
    (x : Sys)
    (hzero : D.recoverHidden (D.hiddenFlow x) = 0) :
    heatLoss B C x = 0 := by
  exact heatLoss_eq_zero_of_actual_eq_ideal B C x
    (D.actual_eq_ideal_of_hidden_zero x hzero)

/-! ## 11. Hidden-information bridge -/

/--
Bridge between visible Bregman heat and hidden commutant information.

This is the exact formal version of:

"heat is information hidden in the mirror's commutant."

It is not a global theorem. It is true once the calibration bridge is supplied.
-/
structure HeatEqualsHiddenInformation
    (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where

  /-- Hidden-sector scalar readout. -/
  hiddenReadout : HiddenInformationReadout Comm

  /--
  Calibration law:

  visible Bregman heat equals hidden-sector information readout.
  -/
  heat_eq_hidden :
    ∀ x : Sys,
      heatLoss B C x =
        hiddenReadout.hiddenInfo (D.hiddenFlow x)

namespace HeatEqualsHiddenInformation

variable
    {Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

/--
Heat is the scalar readout of hidden commutant information once the bridge
datum is supplied.
-/
theorem heat_is_hidden_commutant_information
    (W : HeatEqualsHiddenInformation Sys Comm B C D)
    (x : Sys) :
    heatLoss B C x =
      W.hiddenReadout.hiddenInfo (D.hiddenFlow x) :=
  W.heat_eq_hidden x

/--
The hidden-information readout is nonnegative.
-/
theorem hidden_information_nonneg
    (W : HeatEqualsHiddenInformation Sys Comm B C D)
    (x : Sys) :
    0 ≤ W.hiddenReadout.hiddenInfo (D.hiddenFlow x) :=
  W.hiddenReadout.nonneg _

/--
Heat nonnegativity can also be read through the hidden sector.
-/
theorem heat_nonneg_from_hidden
    (W : HeatEqualsHiddenInformation Sys Comm B C D)
    (x : Sys) :
    0 ≤ heatLoss B C x := by
  rw [W.heat_is_hidden_commutant_information x]
  exact W.hidden_information_nonneg x

end HeatEqualsHiddenInformation

/-! ## 12. Observer readout and loss of distinguishability -/

/--
A distinguishability readout on visible states.

Concrete instances may be trace distance, relative entropy, Bregman divergence,
Fisher distance, or a projective distance.
-/
structure DistinguishabilityDatum
    (Sys : Type*) where
  distinguish : Sys → Sys → ℝ
  nonneg :
    ∀ x y : Sys, 0 ≤ distinguish x y

/--
A dissipative channel contracts or hides visible distinguishability.

The concrete inequality is model-dependent, so it is a proof-carrying field.
-/
structure VisibleDistinguishabilityLoss
    (Sys : Type*) [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    (C : DissipativeChannel Sys)
    (Dg : DistinguishabilityDatum Sys) where
  /--
  Actual dissipative transport does not exceed the ideal distinguishability
  budget.
  -/
  actual_le_ideal :
    ∀ x y : Sys,
      Dg.distinguish (C.actual x) (C.actual y) ≤
        Dg.distinguish (C.ideal x) (C.ideal y)

namespace VisibleDistinguishabilityLoss

variable
    {Sys : Type*} [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    {C : DissipativeChannel Sys}
    {Dg : DistinguishabilityDatum Sys}

/--
Visible distinguishability cannot exceed the ideal budget once the contraction
witness is supplied.
-/
theorem actual_distinguishability_le_ideal
    (L : VisibleDistinguishabilityLoss Sys C Dg)
    (x y : Sys) :
    Dg.distinguish (C.actual x) (C.actual y) ≤
      Dg.distinguish (C.ideal x) (C.ideal y) :=
  L.actual_le_ideal x y

end VisibleDistinguishabilityLoss

/-! ## 13. Dilation-level information accounting -/

/--
A Stinespring/Tomita-style information dilation.

`System` is the observed algebra/state space.

`Dilated` is the enlarged system+environment or algebra+commutant carrier.

`Env` is the inaccessible environment/commutant readout space.

This is not a proof of Stinespring's theorem. It is the proof-carrying socket
where a concrete Stinespring/Tomita dilation is installed.
-/
structure StinespringInformationDilation
    (System Dilated Env : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env] where

  /-- Embed an observed system state into the dilated carrier. -/
  inject : System →L[ℝ] Dilated

  /-- Read out the observed system component from the dilated carrier. -/
  systemPart : Dilated →L[ℝ] System

  /-- Read out the hidden environment/commutant component. -/
  environmentPart : Dilated →L[ℝ] Env

  /-- Conservative dilated evolution. -/
  dilatedFlow : Dilated →L[ℝ] Dilated

  /-- The observed reduced channel. -/
  observedFlow : System →L[ℝ] System

  /-- The observed channel is the system readout of the dilated flow. -/
  observed_factorization :
    ∀ U : System,
      systemPart (dilatedFlow (inject U)) = observedFlow U

  /-- Initially, the system readout recovers the injected state. -/
  systemPart_inject :
    ∀ U : System,
      systemPart (inject U) = U

  /-- Accessible information readout on the observed system. -/
  accessibleInfo : System → ℝ

  /-- Hidden information readout on the environment/commutant branch. -/
  hiddenInfo : Env → ℝ

  /-- Total information readout on the dilated carrier. -/
  totalInfo : Dilated → ℝ

  /-- Total information splits into accessible plus hidden readouts. -/
  total_split :
    ∀ Z : Dilated,
      totalInfo Z =
        accessibleInfo (systemPart Z) +
        hiddenInfo (environmentPart Z)

  /-- Dilated evolution conserves total information. -/
  total_conserved :
    ∀ U : System,
      totalInfo (dilatedFlow (inject U)) =
        totalInfo (inject U)

  /-- The injected initial environment/commutant branch is information-neutral. -/
  environment_initial_zero :
    ∀ U : System,
      hiddenInfo (environmentPart (inject U)) = 0

namespace StinespringInformationDilation

variable
    {System Dilated Env : Type*}
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env]

variable (D : StinespringInformationDilation System Dilated Env)

/--
Accessible information loss equals hidden environment/commutant information.

This is the formal conservation law behind the slogan:

  "the information lost by the observed channel is hidden in the commutant."
-/
theorem accessible_loss_eq_hidden_information
    (U : System) :
    D.accessibleInfo U - D.accessibleInfo (D.observedFlow U) =
      D.hiddenInfo
        (D.environmentPart (D.dilatedFlow (D.inject U))) := by
  let Z₀ : Dilated := D.inject U
  let Z₁ : Dilated := D.dilatedFlow Z₀

  have hinit :
      D.totalInfo Z₀ = D.accessibleInfo U := by
    dsimp [Z₀]
    rw [D.total_split (D.inject U)]
    rw [D.systemPart_inject U]
    rw [D.environment_initial_zero U]
    ring

  have hfinal :
      D.totalInfo Z₁ =
        D.accessibleInfo (D.observedFlow U) +
          D.hiddenInfo (D.environmentPart Z₁) := by
    dsimp [Z₁, Z₀]
    rw [D.total_split (D.dilatedFlow (D.inject U))]
    rw [D.observed_factorization U]

  have hcons :
      D.totalInfo Z₁ = D.totalInfo Z₀ := by
    dsimp [Z₁, Z₀]
    exact D.total_conserved U

  linarith

/-! ## 14. Heat calibration -/

/--
A heat calibration for a Stinespring/Tomita dilation.

This is the extra thermodynamic datum saying that heat is the accessible
information loss of the observed system.
-/
structure HeatCalibration where
  /-- Heat readout on the observed system state. -/
  heat : System → ℝ

  /-- Heat is calibrated as loss of accessible distinguishability. -/
  heat_eq_accessible_loss :
    ∀ U : System,
      heat U =
        D.accessibleInfo U - D.accessibleInfo (D.observedFlow U)

namespace HeatCalibration

variable {D}
variable (C : HeatCalibration D)

/--
Once a heat calibration is supplied, heat equals hidden commutant information.
-/
theorem heat_eq_hidden_information
    (U : System) :
    C.heat U =
      D.hiddenInfo
        (D.environmentPart (D.dilatedFlow (D.inject U))) := by
  rw [C.heat_eq_accessible_loss U]
  exact D.accessible_loss_eq_hidden_information U

end HeatCalibration

/-! ## 15. Bregman heat calibration -/

/--
A Bregman calibration of heat.

The Bregman divergence compares an ideal reversible target with the actual
observed reduced flow.
-/
structure BregmanHeatCalibration where
  /-- Ideal reversible comparison channel. -/
  idealFlow : System →L[ℝ] System

  /-- Bregman divergence readout. -/
  bregman : System → System → ℝ

  /-- Bregman divergence is nonnegative. -/
  bregman_nonneg :
    ∀ X Y : System, 0 ≤ bregman X Y

  /-- Bregman divergence vanishes on the diagonal. -/
  bregman_self :
    ∀ X : System, bregman X X = 0

  /--
  Heat is the Bregman shear between ideal and actual observed evolution.
  -/
  heat_eq_bregman :
    ∀ U : System,
      bregman (idealFlow U) (D.observedFlow U) =
        D.accessibleInfo U - D.accessibleInfo (D.observedFlow U)

namespace BregmanHeatCalibration

variable {D}
variable (B : BregmanHeatCalibration D)

/--
Bregman heat is nonnegative.
-/
theorem bregman_heat_nonneg
    (U : System) :
    0 ≤ B.bregman (B.idealFlow U) (D.observedFlow U) :=
  B.bregman_nonneg _ _

/--
Bregman heat equals hidden commutant information.
-/
theorem bregman_heat_eq_hidden_information
    (U : System) :
    B.bregman (B.idealFlow U) (D.observedFlow U) =
      D.hiddenInfo
        (D.environmentPart (D.dilatedFlow (D.inject U))) := by
  rw [B.heat_eq_bregman U]
  exact D.accessible_loss_eq_hidden_information U

end BregmanHeatCalibration

end StinespringInformationDilation

/-! ## 16. Owner targets -/

/--
Owner target for the Stinespring/Tomita dilation layer.

It is witness-gated: once the dilation is supplied, the visible deficit is
identified with recovered hidden flow.
-/
def StinespringDilationOwnerTarget : Prop :=
  ∀ (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm],
  ∀ (C : DissipativeChannel Sys),
  ∀ (D : StinespringTomitaDilation Sys Comm C),
  ∀ x : Sys,
    C.ideal x - C.actual x =
      D.recoverHidden (D.hiddenFlow x)

/--
The owner target follows from the dilation conservation law.
-/
theorem stinespringDilationOwnerTarget :
    StinespringDilationOwnerTarget := by
  intro Sys Comm _ _ _ _ C D x
  exact D.ideal_sub_actual_eq_recovered_hidden x

/--
Owner target for the heat-hidden-information bridge.
-/
def HeatHiddenInformationOwnerTarget : Prop :=
  ∀ (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm],
  ∀ (B : BregmanDivergenceDatum Sys),
  ∀ (C : DissipativeChannel Sys),
  ∀ (D : StinespringTomitaDilation Sys Comm C),
  ∀ (W : HeatEqualsHiddenInformation Sys Comm B C D),
  ∀ x : Sys,
    heatLoss B C x =
      W.hiddenReadout.hiddenInfo (D.hiddenFlow x)

/--
The heat-hidden-information target follows from the supplied bridge datum.
-/
theorem heatHiddenInformationOwnerTarget :
    HeatHiddenInformationOwnerTarget := by
  intro Sys Comm _ _ _ _ B C D W x
  exact W.heat_is_hidden_commutant_information x

/--
Owner target for supplying a Stinespring/Tomita information dilation.
-/
def StinespringInformationDilationOwnerTarget
    (System Dilated Env : Type*)
    [NormedAddCommGroup System] [NormedSpace ℝ System]
    [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]
    [NormedAddCommGroup Env] [NormedSpace ℝ Env] : Prop :=
  Nonempty (StinespringInformationDilation System Dilated Env)

end InfoGeometry.OperatorAlgebra.StinespringDilation
