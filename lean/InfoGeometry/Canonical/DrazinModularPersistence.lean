import Mathlib.Tactic
import InfoGeometry.Canonical.Drazin
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Meta.Architecture

/-!
# Drazin modular persistence

Drazin support as a modular fixed-point horizon.

Principle:

* the Drazin support `p = A * Aᴰ` is the algebraic support of persistence;
* modular fixedness upgrades that support to a physical horizon;
* horizon zero modes are observables localized on that Drazin horizon;
* Fierz residual vanishing is not inferred from modular fixedness alone, but
  from an explicit compatibility property for horizon zero-mode channels.

This file is an abstract socket.  It does not replace the repo's concrete
Drazin, modular-flow, or Fierz readout owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinModularPersistence

open InfoGeometry.Canonical.Drazin
open InfoGeometry.OperatorAlgebra.Thermodynamics

/-- The theorem-safe zero-mode condition for an abstract modular flow. -/
@[rep_depth operator]
def IsModularZeroMode
    {Obs : Type*} [Ring Obs]
    (flow : ModularFlow Obs)
    (x : Obs) : Prop :=
  ∀ t : ℝ, flow.flow t x = x

/--
Drazin inverse/support data.

`AD` is the Drazin inverse candidate and `p = A * AD` is the Drazin support.
The index is included for general Drazin theory; group-invertible cases use
index `1`.
-/
@[rep_depth operator]
structure DrazinSupportData
    (Obs : Type*) [Ring Obs] [Star Obs] where
  A : Obs
  AD : Obs
  p : Obs
  index : ℕ
  hDrazin : IsDrazinInverse A AD index
  p_def : p = A * AD
  p_self_adjoint : star p = p

namespace DrazinSupportData

variable {Obs : Type*} [Ring Obs] [Star Obs]
variable (D : DrazinSupportData Obs)

/-- The stored support is exactly the canonical Drazin projection. -/
@[rep_depth operator]
theorem p_eq_projection :
    D.p = IsDrazinInverse.projection D.A D.AD := by
  simpa [IsDrazinInverse.projection] using D.p_def

/-- The Drazin support is idempotent. -/
@[rep_depth operator]
theorem p_idempotent :
    D.p * D.p = D.p := by
  rw [D.p_def]
  simpa [IsDrazinInverse.projection] using
    IsDrazinInverse.projection_is_idempotent D.hDrazin

/-- The Drazin complementary projector. -/
@[rep_depth operator]
def q : Obs :=
  1 - D.p

end DrazinSupportData

/--
A Drazin support becomes a physical horizon exactly when it is fixed by the
modular flow.
-/
@[rep_depth operator]
def IsPhysicalHorizon
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs) : Prop :=
  IsModularZeroMode flow D.p

/--
Alias for the physical interpretation:
a Drazin support acts as a modular stability filter exactly when its support
projector is fixed by the modular flow.

This is not a redefinition of the Drazin projector.  It is the extra
modular-zero condition on the already algebraic Drazin support.
-/
@[rep_depth operator]
abbrev IsDrazinModularStabilityFilter
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs) : Prop :=
  IsPhysicalHorizon flow D

/--
Alias for the anomaly-free modular boundary condition.

This is the same condition as `IsPhysicalHorizon`: the Drazin support is fixed
by modular flow.
-/
@[rep_depth operator]
def ModularInvariantDrazinBoundary
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs) : Prop :=
  IsPhysicalHorizon flow D

/--
Leakage from the Drazin horizon into an abstract complement `q`.

`q` is intended to model `1 - p`, but is kept abstract so the theorem only
needs the annihilation law `q * p = 0`.
-/
@[rep_depth operator]
def leakageOperator
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (t : ℝ) : Obs :=
  q * flow.flow t D.p * D.p

/--
If the Drazin horizon is modularly fixed and the complement annihilates it,
there is no leakage.
-/
@[rep_depth operator]
theorem no_leakage_of_physical_horizon
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (hPhys : IsPhysicalHorizon flow D)
    (hOrth : q * D.p = 0) :
    ∀ t : ℝ, leakageOperator flow D q t = 0 := by
  intro t
  unfold IsPhysicalHorizon IsModularZeroMode at hPhys
  unfold leakageOperator
  rw [hPhys t]
  rw [hOrth, zero_mul]

/-! ## Moving Drazin boundaries and covariant sector preservation -/

/--
The covariantly transported Drazin boundary.

When the Drazin support is not fixed by modular flow, the correct cutoff is the
moving boundary `σₜ(p_A)`, not the frozen boundary `p_A`.
-/
@[rep_depth operator]
def movingDrazinBoundary
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (t : ℝ) : Obs :=
  flow.flow t D.p

/--
Alias with the geometric name used in the covariant-horizon formulation.
-/
@[rep_depth operator]
def MovingDrazinBoundary
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (t : ℝ) : Obs :=
  movingDrazinBoundary flow D t

/--
Fixed-frame modular leakage from the original Drazin support into an abstract
complement.

This is definitionally the same operator as `leakageOperator`; the name records
the interpretation: apparent leakage is measured relative to a frozen cutoff.
-/
@[rep_depth operator]
def fixedFrameModularLeakage
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (t : ℝ) : Obs :=
  leakageOperator flow D q t

/--
Alias for the anomaly functional's leakage operator:
`q * σₜ(p_A) * p_A`.
-/
@[rep_depth operator]
def modularLeakageOperator
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (t : ℝ) : Obs :=
  fixedFrameModularLeakage flow D q t

/--
If the Drazin boundary is modular-invariant, fixed-frame leakage vanishes.
-/
@[rep_depth operator]
theorem no_leakage_of_modular_invariant_boundary
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (hInv : ModularInvariantDrazinBoundary flow D)
    (hOrth : q * D.p = 0) :
    ∀ t : ℝ, modularLeakageOperator flow D q t = 0 := by
  exact no_leakage_of_physical_horizon flow D q hInv hOrth

/-- Real expectation/readout state, explicitly not assumed tracial. -/
@[rep_depth operator]
structure RealExpectationState
    (Obs : Type*) [Monoid Obs] [Star Obs] where
  expect : Obs → ℝ
  unital : expect 1 = 1

namespace RealExpectationState

variable {Obs : Type*} [Monoid Obs] [Star Obs]

/-- The state is positive: `φ(A* A) ≥ 0` for all `A`. -/
def positivity
    (φ : RealExpectationState Obs) : Prop :=
  ∀ A : Obs, 0 ≤ φ.expect (star A * A)

end RealExpectationState

/--
Expectation-valued leakage energy.

The state is not assumed tracial; the ordered positive expression is
`φ(Λ* Λ)`.
-/
@[rep_depth operator]
def modularLeakageEnergy
    {Obs : Type*} [Ring Obs] [Star Obs]
    (φ : RealExpectationState Obs)
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (t : ℝ) : ℝ :=
  let Λ := fixedFrameModularLeakage flow D q t
  φ.expect (star Λ * Λ)

/-- Nilpotent square-zero elements remain square-zero under modular transport. -/
@[rep_depth operator]
theorem square_zero_transport
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (N : Obs)
    (t : ℝ)
    (hN : N * N = 0) :
    flow.flow t N * flow.flow t N = 0 := by
  calc
    flow.flow t N * flow.flow t N = flow.flow t (N * N) := by
      exact ((flow.flow t).map_mul N N).symm
    _ = flow.flow t 0 := by rw [hN]
    _ = 0 := by
      exact (flow.flow t).map_zero

/--
Scaled-projector fibers are transported covariantly.

The scalar is kept as an algebra element, so the theorem does not assume an
external complex scalar action on `Obs`.
-/
@[rep_depth operator]
theorem left_scaled_projector_transport
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (M lam : Obs)
    (t : ℝ)
    (hM : M * M = lam * M) :
    flow.flow t M * flow.flow t M =
      flow.flow t lam * flow.flow t M := by
  calc
    flow.flow t M * flow.flow t M = flow.flow t (M * M) := by
      exact ((flow.flow t).map_mul M M).symm
    _ = flow.flow t (lam * M) := by rw [hM]
    _ = flow.flow t lam * flow.flow t M := by
      exact (flow.flow t).map_mul lam M

/-- Two-sided invertibility is preserved by modular transport. -/
@[rep_depth operator]
theorem invertible_transport
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (x : Obs)
    (t : ℝ)
    (hInv : ∃ y : Obs, x * y = 1 ∧ y * x = 1) :
    ∃ y : Obs,
      flow.flow t x * y = 1 ∧ y * flow.flow t x = 1 := by
  rcases hInv with ⟨y, hxy, hyx⟩
  refine ⟨flow.flow t y, ?_, ?_⟩
  · calc
      flow.flow t x * flow.flow t y = flow.flow t (x * y) := by
        exact ((flow.flow t).map_mul x y).symm
      _ = flow.flow t 1 := by rw [hxy]
      _ = 1 := by
        exact (flow.flow t).map_one
  · calc
      flow.flow t y * flow.flow t x = flow.flow t (y * x) := by
        exact ((flow.flow t).map_mul y x).symm
      _ = flow.flow t 1 := by rw [hyx]
      _ = 1 := by
        exact (flow.flow t).map_one

/--
Modular ring-equivalence transport preserves the Drazin inverse laws.

This theorem is the owner-backed replacement for the former transport packet:
the proof is the general Drazin ring-equivalence transport lemma applied to the
modular flow automorphism.
-/
@[rep_depth operator]
theorem modularFlow_transport_isDrazinInverse
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (t : ℝ) :
    IsDrazinInverse (flow.flow t D.A) (flow.flow t D.AD) D.index :=
  IsDrazinInverse.map_ringEquiv (flow.flow t) D.hDrazin

/--
The transported Drazin support is the modular image of the original support.

This is the formal version of `p_{σₜ(A)} = σₜ(p_A)` at the support level.
-/
@[rep_depth operator]
theorem transported_support_eq_moving_boundary
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (t : ℝ) :
    flow.flow t D.A * flow.flow t D.AD =
      movingDrazinBoundary flow D t := by
  unfold movingDrazinBoundary
  rw [D.p_def]
  exact ((flow.flow t).map_mul D.A D.AD).symm

/--
State invariance socket for real expectation readouts.

This is the expectation-only substitute for trace cyclicity/conservation.
-/
@[rep_depth operator]
structure FlowInvariantRealExpectationState
    (Obs : Type*) [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs) where
  state : RealExpectationState Obs
  flow_invariant :
    ∀ t x, state.expect (flow.flow t x) = state.expect x

namespace FlowInvariantRealExpectationState

variable {Obs : Type*} [Ring Obs] [Star Obs]
variable {flow : ModularFlow Obs}
variable (φ : FlowInvariantRealExpectationState Obs flow)

/-- Re-export expectation invariance under the modular flow. -/
@[rep_depth operator]
theorem expect_flow_eq
    (t : ℝ)
    (x : Obs) :
    φ.state.expect (flow.flow t x) = φ.state.expect x :=
  φ.flow_invariant t x

end FlowInvariantRealExpectationState

/-- A physical observable is a zero mode localized on the Drazin horizon. -/
@[rep_depth operator]
def IsHorizonZeroMode
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (x : Obs) : Prop :=
  D.p * x * D.p = x ∧ IsModularZeroMode flow x

/-- Minimal Fierz channel tags for horizon readouts. -/
@[rep_depth operator]
inductive FierzChannel where
  | scalar
  | phase
  | metric
  | area
  deriving DecidableEq, Fintype

/-- Model-supplied Fierz channel map on an observable algebra. -/
@[rep_depth operator]
abbrev FierzChannelMap (Obs : Type*) :=
  FierzChannel → Obs → Obs

def FierzChannelMap.channel {Obs : Type*}
    (C : FierzChannelMap Obs) : FierzChannel → Obs → Obs :=
  C

/-- Expectation-valued Fierz coordinates. -/
@[rep_depth operator]
abbrev FierzCoordinates : Type :=
  FierzChannel → ℝ

def FierzCoordinates.coord (C : FierzCoordinates) : FierzChannel → ℝ :=
  C

/-- Abstract Fierz residual functional. -/
@[rep_depth operator]
abbrev FierzResidual : Type :=
  FierzCoordinates → ℝ

def FierzResidual.residual (R : FierzResidual) : FierzCoordinates → ℝ :=
  R

/-- Fierz channels are admissible when each channel is a horizon zero mode. -/
@[rep_depth operator]
def ChannelsAreHorizonZeroModes
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (C : FierzChannelMap Obs) : Prop :=
  ∀ ch : FierzChannel, IsHorizonZeroMode flow D (C.channel ch D.AD)

/-- Expectation-valued Fierz coordinates on the Drazin horizon. -/
@[rep_depth operator]
def horizonFierzVector
    {Obs : Type*} [Ring Obs] [Star Obs]
    (φA : RealExpectationState Obs)
    (C : FierzChannelMap Obs)
    (D : DrazinSupportData Obs) :
    FierzCoordinates :=
  fun ch => φA.expect (C.channel ch D.AD)

/--
Compatibility property for the model-specific Fierz identity.

This is not an owner-derived theorem.  It is an explicitly named property
packet.  Modular fixedness of the Drazin support alone gives no-leakage, not a
Fierz identity.
-/
@[rep_depth operator]
structure HorizonFierzCompatibilityAssumption
    (Obs : Type*) [Ring Obs] [Star Obs] where
  flow : ModularFlow Obs
  compressedState : RealExpectationState Obs
  channels : FierzChannelMap Obs
  residual : FierzResidual
  compatibility_property :
    ∀ D : DrazinSupportData Obs,
      IsPhysicalHorizon flow D →
      ChannelsAreHorizonZeroModes flow D channels →
        residual.residual (horizonFierzVector compressedState channels D) = 0

/--
Assumption-derived Fierz readback.

If the Drazin support is a modular physical horizon, the Fierz channels are
horizon zero modes, and the explicit compatibility property is supplied, then
the compressed expectation vector satisfies the supplied Fierz residual law.
-/
@[rep_depth operator]
theorem fierz_quadric_from_modular_physical_horizon_property
    {Obs : Type*} [Ring Obs] [Star Obs]
    (K : HorizonFierzCompatibilityAssumption Obs)
    (D : DrazinSupportData Obs)
    (hHorizon : IsPhysicalHorizon K.flow D)
    (hChannels : ChannelsAreHorizonZeroModes K.flow D K.channels) :
    K.residual.residual (horizonFierzVector K.compressedState K.channels D) = 0 :=
  K.compatibility_property D hHorizon hChannels

end InfoGeometry.Canonical.DrazinModularPersistence
