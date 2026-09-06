/-
InfoGeometry/OperatorAlgebra/SpinBogoliubovStinespring.lean

Spin connection as Bogoliubov frame selector.

This module records the bridge:

  spin connection
      -> transported Clifford/spin frame
      -> Bogoliubov frame change
      -> open-system channel after observer reduction
      -> Stinespring/Tomita hidden-sector accounting.

It does not assert that every spin connection causes thermodynamic loss.
Loss/heat appears only after a reduction and a calibrated Stinespring/Bregman
readout.
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpinBogoliubovStinespring

open InfoGeometry.OperatorAlgebra.StinespringDilation

/-! ## 1. Spin-frame and Bogoliubov-frame carriers -/

/--
A local spin/Clifford frame.

`Frame` is deliberately abstract: concrete models may instantiate it by a
vierbein/tetrad, Clifford frame, Majorana mode frame, or polarization frame.
-/
@[rep_depth operator]
structure LocalSpinFrame
    (Frame : Type*) where
  /-- Underlying local frame representative. -/
  frame : Frame

/--
A Bogoliubov frame on a state/operator module.

The two maps represent the two complementary halves of the frame, e.g.
annihilation/creation, system/commutant, or positive/negative modes.
-/
@[rep_depth operator]
structure BogoliubovFrame
    (Mode State : Type*) [AddCommGroup State] [Module ℝ State] where
  /-- Annihilation, system, or positive-frequency half of the splitting. -/
  annihilator : Mode → State

  /-- Creation, commutant, or negative-frequency half of the splitting. -/
  creator : Mode → State

/--
A spin connection transports spin frames.

This is the geometric input. It is not, by itself, a Stinespring dilation.
-/
@[rep_depth operator]
structure SpinConnectionTransport
    (Base Frame : Type*) where
  /-- Transport a frame between two base points. -/
  transport : Base → Base → Frame → Frame

/-! ## 1a. Dimension-agnostic constructive owners -/

section DimensionAgnosticConstructors

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndN" =>
  InfoGeometry.Krein.NeutralSpace E →L[ℝ] InfoGeometry.Krein.NeutralSpace E
local notation "EndH" =>
  InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E

/--
The concrete spin-connection transport on neutral-space endomorphisms.

This replaces the abstract preservation hypothesis by the existing
dimension-agnostic transport theorems from `Canonical.SpinConnection`.
-/
noncomputable def spinConnectionEndTransport
    (S : InfoGeometry.Canonical.SpinConnection E) :
    SpinConnectionTransport ℝ EndN where
  transport := fun s t A =>
    InfoGeometry.Canonical.transportEnd S (t - s) A

@[simp] theorem spinConnectionEndTransport_apply
    (S : InfoGeometry.Canonical.SpinConnection E)
    (s t : ℝ) (A : EndN) :
    (spinConnectionEndTransport (E := E) S).transport s t A =
      InfoGeometry.Canonical.transportEnd S (t - s) A :=
  rfl

@[simp] theorem spinConnectionEndTransport_add
    (S : InfoGeometry.Canonical.SpinConnection E)
    (s t : ℝ) (A B : EndN) :
    (spinConnectionEndTransport (E := E) S).transport s t (A + B) =
      (spinConnectionEndTransport (E := E) S).transport s t A +
        (spinConnectionEndTransport (E := E) S).transport s t B :=
  InfoGeometry.Canonical.transportEnd_add S (t - s) A B

@[simp] theorem spinConnectionEndTransport_mul
    (S : InfoGeometry.Canonical.SpinConnection E)
    (s t : ℝ) (A B : EndN) :
    (spinConnectionEndTransport (E := E) S).transport s t (A * B) =
      (spinConnectionEndTransport (E := E) S).transport s t A *
        (spinConnectionEndTransport (E := E) S).transport s t B :=
  InfoGeometry.Canonical.transportEnd_mul S (t - s) A B

@[simp] theorem spinConnectionEndTransport_lie
    (S : InfoGeometry.Canonical.SpinConnection E)
    (s t : ℝ) (A B : EndN) :
    (spinConnectionEndTransport (E := E) S).transport s t ⁅A, B⁆ =
      ⁅(spinConnectionEndTransport (E := E) S).transport s t A,
        (spinConnectionEndTransport (E := E) S).transport s t B⁆ :=
  InfoGeometry.Canonical.transportEnd_lie S (t - s) A B

@[simp] theorem spinConnectionEndTransport_U_zero
    (S : InfoGeometry.Canonical.SpinConnection E) :
    S.U 0 = 1 :=
  S.U_zero

theorem spinConnectionEndTransport_U_add
    (S : InfoGeometry.Canonical.SpinConnection E) (s t : ℝ) :
    S.U (s + t) = S.U s * S.U t :=
  S.U_add s t

/--
Canonical phase Bogoliubov splitting on the doubled real carrier.

The two halves are not hypotheses: they are the constructive projectors
`phaseLinearPart` and `phaseAntilinearPart`, and their reconstruction plus
linearity/antilinearity certificates are proved in `BogoliubovTransport`.
-/
noncomputable def canonicalPhaseBogoliubovFrame :
    BogoliubovFrame EndH EndH where
  annihilator :=
    InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart (E := E)
  creator :=
    InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart (E := E)

omit [CompleteSpace E] in
@[simp] theorem canonicalPhaseBogoliubovFrame_annihilator
    (A : EndH) :
    (canonicalPhaseBogoliubovFrame (E := E)).annihilator A =
      InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart (E := E) A :=
  rfl

omit [CompleteSpace E] in
@[simp] theorem canonicalPhaseBogoliubovFrame_creator
    (A : EndH) :
    (canonicalPhaseBogoliubovFrame (E := E)).creator A =
      InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart (E := E) A :=
  rfl

omit [CompleteSpace E] in
theorem canonicalPhaseBogoliubovFrame_reconstruct
    (A : EndH) :
    (canonicalPhaseBogoliubovFrame (E := E)).annihilator A
      + (canonicalPhaseBogoliubovFrame (E := E)).creator A = A :=
  InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart_add_phaseAntilinearPart
    (E := E) A

omit [CompleteSpace E] in
theorem canonicalPhaseBogoliubovFrame_annihilator_phaseLinear
    (A : EndH) :
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E)
      ((canonicalPhaseBogoliubovFrame (E := E)).annihilator A) :=
  InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart_isPhaseLinear
    (E := E) A

omit [CompleteSpace E] in
theorem canonicalPhaseBogoliubovFrame_creator_phaseAntilinear
    (A : EndH) :
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseAntilinear (E := E)
      ((canonicalPhaseBogoliubovFrame (E := E)).creator A) :=
  InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart_isPhaseAntilinear
    (E := E) A

end DimensionAgnosticConstructors

/--
A calibration saying that a transported spin frame determines a Bogoliubov
frame.
-/
@[rep_depth operator]
structure SpinFrameBogoliubovCalibration
    (Base Frame Mode State : Type*)
    [AddCommGroup State] [Module ℝ State] where
  /-- Spin connection transport of the local spin/Clifford frame. -/
  spinTransport : SpinConnectionTransport Base Frame

  /-- Convert a local spin frame into a Bogoliubov frame. -/
  bogoliubovOfFrame : Frame → BogoliubovFrame Mode State

/-! ## 2. Frame mismatch and induced open channel -/

/--
A Bogoliubov frame mismatch between two base points.

This is where particle/commutant/environment mixing enters.
-/
@[rep_depth operator]
structure BogoliubovFrameMismatch
    (Base Frame Mode State : Type*)
    [AddCommGroup State] [Module ℝ State]
    (C : SpinFrameBogoliubovCalibration Base Frame Mode State) where
  /-- Source base point. -/
  source : Base

  /-- Target base point. -/
  target : Base

  /-- Source spin/Clifford frame. -/
  sourceFrame : Frame

  /-- Transported target frame. -/
  transportedFrame : Frame

  /-- The transported frame is obtained by the spin connection. -/
  transportedFrame_eq :
    transportedFrame = C.spinTransport.transport source target sourceFrame

  /-- Source Bogoliubov frame. -/
  sourceBogoliubov :
    BogoliubovFrame Mode State

  /-- Source Bogoliubov frame is selected by the source spin frame. -/
  sourceBogoliubov_eq :
    sourceBogoliubov = C.bogoliubovOfFrame sourceFrame

  /-- Target Bogoliubov frame. -/
  targetBogoliubov :
    BogoliubovFrame Mode State

  /-- Target Bogoliubov frame is selected by the transported spin frame. -/
  targetBogoliubov_eq :
    targetBogoliubov = C.bogoliubovOfFrame transportedFrame

  /-- Model-specific readout saying the two Bogoliubov splittings differ. -/
  mismatchReadout : State → State

namespace BogoliubovFrameMismatch

variable {Base Frame Mode State : Type*} [AddCommGroup State] [Module ℝ State]
variable {C : SpinFrameBogoliubovCalibration Base Frame Mode State}
variable (M : BogoliubovFrameMismatch Base Frame Mode State C)

/-- The transported frame is the spin-connection transport of the source frame. -/
theorem transportedFrame_eq_transport :
    M.transportedFrame = C.spinTransport.transport M.source M.target M.sourceFrame :=
  M.transportedFrame_eq

/-- The source Bogoliubov frame is selected by the source spin frame. -/
theorem sourceBogoliubov_eq_bogoliubovOfFrame :
    M.sourceBogoliubov = C.bogoliubovOfFrame M.sourceFrame :=
  M.sourceBogoliubov_eq

/-- The target Bogoliubov frame is selected by the transported spin frame. -/
theorem targetBogoliubov_eq_bogoliubovOfFrame :
    M.targetBogoliubov = C.bogoliubovOfFrame M.transportedFrame :=
  M.targetBogoliubov_eq

end BogoliubovFrameMismatch

/--
An open channel induced by a spin/Bogoliubov frame mismatch.

This is the observer-reduced channel. It is not assumed to be lossless.
-/
@[rep_depth operator]
structure SpinInducedOpenChannel
    (Base Frame Mode State : Type*)
    [AddCommGroup State] [Module ℝ State]
    (C : SpinFrameBogoliubovCalibration Base Frame Mode State) where
  /-- Bogoliubov frame mismatch induced by spin-frame transport. -/
  mismatch :
    BogoliubovFrameMismatch Base Frame Mode State C

  /-- Observer-reduced open-system channel. -/
  channel :
    OpenSystemChannel State

/-! ## 3. Stinespring-Tomita accounting for spin-induced channels -/

/--
A Stinespring/Tomita accounting package for a spin-induced channel.

The hidden sector is where the distinguishability lost from the observed
Bogoliubov frame is stored.
-/
@[rep_depth operator]
structure SpinBogoliubovStinespringClinch
    (Base Frame Mode State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : SpinFrameBogoliubovCalibration Base Frame Mode State) where
  /-- Spin-connection/Bogoliubov induced open channel. -/
  spinChannel :
    SpinInducedOpenChannel Base Frame Mode State C

  /-- Stinespring/Tomita dilation of the induced open channel. -/
  dilation :
    StinespringDilation State Env Joint spinChannel.channel

namespace SpinBogoliubovStinespringClinch

variable {Base Frame Mode State Env Joint : Type*}
variable [AddCommGroup State] [Module ℝ State]
variable [AddCommGroup Env] [Module ℝ Env]
variable [AddCommGroup Joint] [Module ℝ Joint]
variable {C : SpinFrameBogoliubovCalibration Base Frame Mode State}
variable (S : SpinBogoliubovStinespringClinch Base Frame Mode State Env Joint C)

/--
The observed deficit of the spin-induced open channel is exactly the mirrored
hidden component supplied by the Stinespring dilation.
-/
theorem spin_deficit_eq_hidden_component
    (x : State) :
    S.spinChannel.channel.ideal x - S.spinChannel.channel.actual x =
      S.dilation.mirroredHiddenComponent x :=
  S.dilation.ideal_sub_actual_eq_mirroredHidden x

/--
If the hidden component vanishes, the spin-induced observed channel agrees with
the ideal reference at that state.
-/
theorem actual_eq_ideal_of_zero_hidden_component
    {x : State}
    (hzero : S.dilation.mirroredHiddenComponent x = 0) :
    S.spinChannel.channel.actual x =
      S.spinChannel.channel.ideal x :=
  S.dilation.actual_eq_ideal_of_zero_mirroredHidden hzero

end SpinBogoliubovStinespringClinch

/-! ## 4. Modular compatibility -/

/--
Compatibility between spatial spin connection and modular flow.

This is the formal place for the statement:

  spin connection = spatial manifestation of modular flow

but only after a model supplies the covariance law.
-/
@[rep_depth operator]
structure SpinModularCompatibility
    (Base Frame State : Type*)
    [AddCommGroup State] [Module ℝ State] where
  /-- Spatial spin-frame transport. -/
  spinTransport : SpinConnectionTransport Base Frame

  /-- Modular/time evolution on the state carrier. -/
  modularFlow : ℝ → State → State

/-! ## 5. Thermodynamic bridge -/

/--
Thermodynamic readout for a spin-induced Bogoliubov/Stinespring channel.

This connects the hidden component to Bregman heat/entropy production.
-/
@[rep_depth operator]
structure SpinBogoliubovThermodynamicReadout
    (Base Frame Mode State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : SpinFrameBogoliubovCalibration Base Frame Mode State)
    (S : SpinBogoliubovStinespringClinch Base Frame Mode State Env Joint C) where
  /-- Bregman backend for heat/information loss. -/
  bregman :
    BregmanBackend State

  /-- Hidden-information readout on the environment/commutant carrier. -/
  hiddenReadout :
    HiddenInformationReadout Env

  /-- Calibration equating Bregman heat with hidden information. -/
  heatHiddenBridge :
    HeatHiddenInformationBridge
      State Env Joint
      bregman
      S.spinChannel.channel
      S.dilation
      hiddenReadout

namespace SpinBogoliubovThermodynamicReadout

variable {Base Frame Mode State Env Joint : Type*}
variable [AddCommGroup State] [Module ℝ State]
variable [AddCommGroup Env] [Module ℝ Env]
variable [AddCommGroup Joint] [Module ℝ Joint]
variable {C : SpinFrameBogoliubovCalibration Base Frame Mode State}
variable {S : SpinBogoliubovStinespringClinch Base Frame Mode State Env Joint C}
variable (T : SpinBogoliubovThermodynamicReadout Base Frame Mode State Env Joint C S)

/--
For a calibrated spin/Bogoliubov/Stinespring model, Bregman heat equals hidden
environment/commutant information.
-/
theorem heat_eq_hidden_information
    (x : State) :
    bregmanHeatLoss T.bregman S.spinChannel.channel x =
      hiddenInformation S.dilation T.hiddenReadout x :=
  HeatHiddenInformationBridge.heat_is_hidden_information T.heatHiddenBridge x

/--
The spin-induced Bregman heat is nonnegative.
-/
theorem heat_nonneg
    (x : State) :
    0 ≤ bregmanHeatLoss T.bregman S.spinChannel.channel x :=
  HeatHiddenInformationBridge.heat_nonneg_from_hidden T.heatHiddenBridge x

end SpinBogoliubovThermodynamicReadout

/-! ## 6. Stinespring-Tomita information ledger -/

/--
Abstract spin-connection datum.

The connection is the geometric/Bogoliubov frame setter. It is not a
Stinespring dilation and it is not, by itself, an Einstein equation.
-/
@[rep_depth operator]
structure SpinConnectionDatum
    (Connection : Type*) where
  /-- The spin connection / Bogoliubov frame setter. -/
  omega : Connection

/--
Two transports on the same operator module.

`modular` is the modular/thermodynamic clock and `spin` is the spin-parallel
transport. Their failure to commute is the spin/modular shear.
-/
@[rep_depth operator]
structure SpinModularTransport
    (Op : Type*) [AddCommGroup Op] [Module ℝ Op] where
  /-- Modular/time transport. -/
  modular : ℝ → Op →ₗ[ℝ] Op

  /-- Spin-frame transport. -/
  spin : ℝ → Op →ₗ[ℝ] Op

  /-- The modular transport is identity at zero time. -/
  modular_zero :
    ∀ x : Op, modular 0 x = x

  /-- The spin transport is identity at zero time. -/
  spin_zero :
    ∀ x : Op, spin 0 x = x

namespace SpinModularTransport

variable {Op : Type*} [AddCommGroup Op] [Module ℝ Op]
variable (T : SpinModularTransport Op)

/-- The spin/modular shear: `modular_t (spin_s x) - spin_s (modular_t x)`. -/
def shear
    (t s : ℝ)
    (x : Op) : Op :=
  T.modular t (T.spin s x) - T.spin s (T.modular t x)

/-- The two transports commute at `(t,s,x)`. -/
def CommutesAt
    (t s : ℝ)
    (x : Op) : Prop :=
  T.modular t (T.spin s x) = T.spin s (T.modular t x)

/-- If the transports commute at `(t,s,x)`, the shear vanishes there. -/
theorem shear_eq_zero_of_commutesAt
    {t s : ℝ}
    {x : Op}
    (h : T.CommutesAt t s x) :
    T.shear t s x = 0 := by
  dsimp [shear, CommutesAt] at h ⊢
  rw [h]
  simp

/-- Nonzero shear means the modular and spin transports fail to commute. -/
theorem not_commutesAt_of_shear_ne_zero
    {t s : ℝ}
    {x : Op}
    (h : T.shear t s x ≠ 0) :
    ¬ T.CommutesAt t s x := by
  intro hc
  exact h (T.shear_eq_zero_of_commutesAt hc)

end SpinModularTransport

/--
A local observable channel.

This is the algebraic carrier for a linear local observable map. Positivity
requires a separate operator-algebra owner theorem.
-/
@[rep_depth operator]
structure LocalChannel
    (Op : Type*) [AddCommGroup Op] [Module ℝ Op] where
  /-- The local observable map. -/
  map : Op →ₗ[ℝ] Op

namespace LocalChannel

variable {Op : Type*} [AddCommGroup Op] [Module ℝ Op]
variable (Φ : LocalChannel Op)

/-- An operator is locally lost/absorbed if the local channel maps it to zero. -/
def IsLocallyLost
    (x : Op) : Prop :=
  Φ.map x = 0

end LocalChannel

/--
A Stinespring-style global ledger.

The local channel is the compression of a global evolution. The accounting law
splits the global evolved representative into the visible embedded output and a
hidden leakage component.
-/
@[rep_depth operator]
structure StinespringLedger
    (Op GlobalOp : Type*)
    [AddCommGroup Op] [Module ℝ Op]
    [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
    (Φ : LocalChannel Op) where
  /-- Embed a local observable into the global bookkeeping space. -/
  embed : Op →ₗ[ℝ] GlobalOp

  /-- Compress the global bookkeeping space back to the local observer. -/
  compress : GlobalOp →ₗ[ℝ] Op

  /-- Global information-preserving evolution. -/
  globalEvolution : GlobalOp →ₗ[ℝ] GlobalOp

  /-- Local channel is compression of global evolution. -/
  channel_factorization :
    ∀ x : Op,
      Φ.map x = compress (globalEvolution (embed x))

  /-- Hidden part of the global evolution. -/
  leakage : Op → GlobalOp

  /-- Global accounting: evolved state is visible output plus hidden leakage. -/
  accounting :
    ∀ x : Op,
      globalEvolution (embed x) =
        embed (Φ.map x) + leakage x

namespace StinespringLedger

variable {Op GlobalOp : Type*}
variable [AddCommGroup Op] [Module ℝ Op]
variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
variable {Φ : LocalChannel Op}
variable (L : StinespringLedger Op GlobalOp Φ)

/-- The channel is the local compression of the global evolution. -/
theorem channel_eq_compressed_global
    (x : Op) :
    Φ.map x = L.compress (L.globalEvolution (L.embed x)) :=
  L.channel_factorization x

/--
If the local channel loses `x`, then the global evolved object is exactly the
leakage component.
-/
theorem locally_lost_global_eq_leakage
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    L.globalEvolution (L.embed x) = L.leakage x := by
  dsimp [LocalChannel.IsLocallyLost] at hx
  rw [L.accounting x, hx]
  simp

end StinespringLedger

/--
A linear scalar readout of the global ledger.

Concrete models may instantiate this by a trace, weight, core trace,
supertrace, zeta-regularized readout, or signed flux backend.
-/
@[rep_depth operator]
structure GlobalReadout
    (GlobalOp : Type*) [AddCommGroup GlobalOp] [Module ℝ GlobalOp] where
  /-- Scalar readout of global observables. -/
  read : GlobalOp →ₗ[ℝ] ℝ

namespace GlobalReadout

variable {Op GlobalOp : Type*}
variable [AddCommGroup Op] [Module ℝ Op]
variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
variable {Φ : LocalChannel Op}
variable (R : GlobalReadout GlobalOp)
variable (L : StinespringLedger Op GlobalOp Φ)

/-- The total readout decomposes into visible local output plus hidden leakage. -/
theorem readout_ledger_decomposition
    (x : Op) :
    R.read (L.globalEvolution (L.embed x)) =
      R.read (L.embed (Φ.map x)) + R.read (L.leakage x) := by
  rw [L.accounting x]
  exact R.read.map_add (L.embed (Φ.map x)) (L.leakage x)

/-- If `x` is locally lost, the total readout is carried by hidden leakage. -/
theorem readout_of_locally_lost
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    R.read (L.globalEvolution (L.embed x)) =
      R.read (L.leakage x) := by
  rw [L.locally_lost_global_eq_leakage hx]

end GlobalReadout

/--
A minimal Tomita routing datum.

`M` is the observable side and `Mcomm` is the commutant/environment side.
-/
@[rep_depth operator]
structure TomitaRouting
    (GlobalOp : Type*) where
  /-- Observable-side region. -/
  M : Set GlobalOp

  /-- Commutant/environment-side region. -/
  Mcomm : Set GlobalOp

  /-- Tomita mirror, morally `x ↦ J x J`. -/
  Jconj : GlobalOp → GlobalOp

  /-- The Tomita mirror sends observable-side data to the commutant. -/
  J_maps_M_to_comm :
    ∀ x : GlobalOp, x ∈ M → Jconj x ∈ Mcomm

/-- A Stinespring ledger whose hidden part is routed into the Tomita commutant. -/
@[rep_depth operator]
structure StinespringTomitaLedger
    (Op GlobalOp : Type*)
    [AddCommGroup Op] [Module ℝ Op]
    [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
    (Φ : LocalChannel Op) where
  /-- Stinespring/global information ledger. -/
  ledger : StinespringLedger Op GlobalOp Φ

  /-- Tomita observable/commutant routing. -/
  tomita : TomitaRouting GlobalOp

  /-- Embedded local observables are in the observable side. -/
  embed_mem_M :
    ∀ x : Op, ledger.embed x ∈ tomita.M

  /-- Leakage is routed into the commutant. -/
  leakage_mem_commutant :
    ∀ x : Op, ledger.leakage x ∈ tomita.Mcomm

namespace StinespringTomitaLedger

variable {Op GlobalOp : Type*}
variable [AddCommGroup Op] [Module ℝ Op]
variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
variable {Φ : LocalChannel Op}
variable (L : StinespringTomitaLedger Op GlobalOp Φ)

/--
If the local observer loses `x`, the global evolved representative is in the
Tomita commutant.
-/
theorem locally_lost_routes_to_commutant
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    L.ledger.globalEvolution (L.ledger.embed x) ∈ L.tomita.Mcomm := by
  rw [L.ledger.locally_lost_global_eq_leakage hx]
  exact L.leakage_mem_commutant x

/-- The embedded input starts on the observable side. -/
theorem input_starts_in_M
    (x : Op) :
    L.ledger.embed x ∈ L.tomita.M :=
  L.embed_mem_M x

end StinespringTomitaLedger

/--
The combined frame.

`omega` sets the Bogoliubov/spin frame, `transport` measures spin/modular
shear, and `ledger` closes information accounting through Stinespring-Tomita
routing.
-/
@[rep_depth operator]
structure SpinBogoliubovStinespringFrame
    (Connection Op GlobalOp : Type*)
    [AddCommGroup Op] [Module ℝ Op]
    [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
    (Φ : LocalChannel Op) where
  /-- Spin connection / Bogoliubov frame setter. -/
  omega : SpinConnectionDatum Connection

  /-- Modular/spin transport pair. -/
  transport : SpinModularTransport Op

  /-- Stinespring-Tomita ledger. -/
  ledger : StinespringTomitaLedger Op GlobalOp Φ

namespace SpinBogoliubovStinespringFrame

variable {Connection Op GlobalOp : Type*}
variable [AddCommGroup Op] [Module ℝ Op]
variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]
variable {Φ : LocalChannel Op}
variable (F : SpinBogoliubovStinespringFrame Connection Op GlobalOp Φ)

/-- Local loss is globally routed into the Tomita commutant. -/
theorem locally_lost_routes_to_commutant
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    F.ledger.ledger.globalEvolution (F.ledger.ledger.embed x) ∈
      F.ledger.tomita.Mcomm :=
  F.ledger.locally_lost_routes_to_commutant hx

/-- Spin/modular shear is the obstruction to the two transports commuting. -/
theorem transport_not_commuting_of_shear_ne_zero
    {t s : ℝ}
    {x : Op}
    (h : F.transport.shear t s x ≠ 0) :
    ¬ F.transport.CommutesAt t s x :=
  F.transport.not_commutesAt_of_shear_ne_zero h

end SpinBogoliubovStinespringFrame

/-! ## 7. Einstein-readout bridge carrier -/

/--
A future bridge from spin/modular shear to effective geometric curvature.

Stinespring gives accounting; this bridge is what would turn accounting/shear
into an Einstein-type consistency law.
-/
@[rep_depth operator]
structure EinsteinReadoutBridge
    (Op Tensor : Type*) [AddCommGroup Op] [Module ℝ Op] where
  /-- Curvature/Einstein tensor readout from spin/modular shear. -/
  curvatureReadout : Op → Tensor

  /-- Stress-energy/flux readout from operator data. -/
  stressReadout : Op → Tensor

  /-- Cosmological/global tear readout. -/
  cosmologicalReadout : Tensor

attribute [rep_depth operator]
  LocalSpinFrame
  BogoliubovFrame
  SpinConnectionTransport
  spinConnectionEndTransport
  spinConnectionEndTransport_apply
  spinConnectionEndTransport_add
  spinConnectionEndTransport_mul
  spinConnectionEndTransport_lie
  spinConnectionEndTransport_U_zero
  spinConnectionEndTransport_U_add
  canonicalPhaseBogoliubovFrame
  canonicalPhaseBogoliubovFrame_annihilator
  canonicalPhaseBogoliubovFrame_creator
  canonicalPhaseBogoliubovFrame_reconstruct
  canonicalPhaseBogoliubovFrame_annihilator_phaseLinear
  canonicalPhaseBogoliubovFrame_creator_phaseAntilinear
  SpinFrameBogoliubovCalibration
  BogoliubovFrameMismatch
  BogoliubovFrameMismatch.transportedFrame_eq_transport
  BogoliubovFrameMismatch.sourceBogoliubov_eq_bogoliubovOfFrame
  BogoliubovFrameMismatch.targetBogoliubov_eq_bogoliubovOfFrame
  SpinInducedOpenChannel
  SpinBogoliubovStinespringClinch
  SpinBogoliubovStinespringClinch.spin_deficit_eq_hidden_component
  SpinBogoliubovStinespringClinch.actual_eq_ideal_of_zero_hidden_component
  SpinModularCompatibility
  SpinBogoliubovThermodynamicReadout
  SpinBogoliubovThermodynamicReadout.heat_eq_hidden_information
  SpinBogoliubovThermodynamicReadout.heat_nonneg
  SpinConnectionDatum
  SpinModularTransport
  SpinModularTransport.shear
  SpinModularTransport.CommutesAt
  SpinModularTransport.shear_eq_zero_of_commutesAt
  SpinModularTransport.not_commutesAt_of_shear_ne_zero
  LocalChannel
  LocalChannel.IsLocallyLost
  StinespringLedger
  StinespringLedger.channel_eq_compressed_global
  StinespringLedger.locally_lost_global_eq_leakage
  GlobalReadout
  GlobalReadout.readout_ledger_decomposition
  GlobalReadout.readout_of_locally_lost
  TomitaRouting
  StinespringTomitaLedger
  StinespringTomitaLedger.locally_lost_routes_to_commutant
  StinespringTomitaLedger.input_starts_in_M
  SpinBogoliubovStinespringFrame
  SpinBogoliubovStinespringFrame.locally_lost_routes_to_commutant
  SpinBogoliubovStinespringFrame.transport_not_commuting_of_shear_ne_zero
  EinsteinReadoutBridge

end InfoGeometry.OperatorAlgebra.SpinBogoliubovStinespring
