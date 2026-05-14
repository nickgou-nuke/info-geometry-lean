import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# Drazin modular persistence

Drazin support as a modular fixed-point horizon.

Principle:

* the Drazin support `p = A * Aᴰ` is the algebraic support of persistence;
* modular fixedness upgrades that support to a physical horizon;
* horizon zero modes are observables localized on that Drazin horizon;
* Fierz residual vanishing is not inferred from modular fixedness alone, but
  from an explicit compatibility witness for horizon zero-mode channels.

This file is an abstract socket.  It does not replace the repo's concrete
Drazin, modular-flow, or Fierz readout owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinModularPersistence

/-- Abstract modular flow `σᵠ_t` on a multiplicative observable algebra. -/
@[rep_depth operator]
structure ModularFlow
    (Obs : Type*) [Monoid Obs] where
  sigma : ℝ → Obs ≃* Obs
  sigma_zero : sigma 0 = MulEquiv.refl Obs
  sigma_add : ∀ s t : ℝ, sigma (s + t) = (sigma s).trans (sigma t)

/-- The theorem-safe zero-mode condition for an abstract modular flow. -/
@[rep_depth operator]
def IsModularZeroMode
    {Obs : Type*} [Monoid Obs]
    (flow : ModularFlow Obs)
    (x : Obs) : Prop :=
  ∀ t : ℝ, flow.sigma t x = x

/--
Drazin inverse/support data.

`AD` is the Drazin inverse candidate and `p = A * AD` is the Drazin support.
The index is included for general Drazin theory; group-invertible cases use
index `1`.
-/
@[rep_depth operator]
structure DrazinSupportData
    (Obs : Type*) [Monoid Obs] [Star Obs] where
  A : Obs
  AD : Obs
  p : Obs
  index : ℕ
  drazin_power_law : A ^ (index + 1) * AD = A ^ index
  drazin_reflexive : AD * A * AD = AD
  drazin_commute : A * AD = AD * A
  p_def : p = A * AD
  p_idempotent : p * p = p
  p_self_adjoint : star p = p

/--
A Drazin support becomes a physical horizon exactly when it is fixed by the
modular flow.
-/
@[rep_depth operator]
def IsPhysicalHorizon
    {Obs : Type*} [Monoid Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs) : Prop :=
  IsModularZeroMode flow D.p

/--
Leakage from the Drazin horizon into an abstract complement `q`.

`q` is intended to model `1 - p`, but is kept abstract so the theorem only
needs the annihilation law `q * p = 0`.
-/
@[rep_depth operator]
def leakageOperator
    {Obs : Type*} [MonoidWithZero Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (q : Obs)
    (t : ℝ) : Obs :=
  q * flow.sigma t D.p * D.p

/--
If the Drazin horizon is modularly fixed and the complement annihilates it,
there is no leakage.
-/
@[rep_depth operator]
theorem no_leakage_of_physical_horizon
    {Obs : Type*} [MonoidWithZero Obs] [Star Obs]
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

/-- A physical observable is a zero mode localized on the Drazin horizon. -/
@[rep_depth operator]
def IsHorizonZeroMode
    {Obs : Type*} [Monoid Obs] [Star Obs]
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
structure FierzChannelMap
    (Obs : Type*) where
  channel : FierzChannel → Obs → Obs

/-- Expectation-valued Fierz coordinates. -/
@[rep_depth operator]
structure FierzCoordinates where
  coord : FierzChannel → ℂ

/-- Abstract Fierz residual functional. -/
@[rep_depth operator]
structure FierzResidual where
  residual : FierzCoordinates → ℝ

/-- Expectation state, explicitly not assumed tracial. -/
@[rep_depth operator]
structure ExpectationState
    (Obs : Type*) [One Obs] [Mul Obs] [Star Obs] [AddCommMonoid Obs] [SMul ℂ Obs] where
  expect : Obs → ℂ
  unital : expect 1 = 1
  positive : ∀ a : Obs, 0 ≤ (expect (star a * a)).re

/-- Fierz channels are admissible when each channel is a horizon zero mode. -/
@[rep_depth operator]
def ChannelsAreHorizonZeroModes
    {Obs : Type*} [Monoid Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (C : FierzChannelMap Obs) : Prop :=
  ∀ ch : FierzChannel, IsHorizonZeroMode flow D (C.channel ch D.AD)

/-- Expectation-valued Fierz coordinates on the Drazin horizon. -/
@[rep_depth operator]
def horizonFierzVector
    {Obs : Type*} [Monoid Obs] [Star Obs] [AddCommMonoid Obs] [SMul ℂ Obs]
    (φA : ExpectationState Obs)
    (C : FierzChannelMap Obs)
    (D : DrazinSupportData Obs) :
    FierzCoordinates where
  coord := fun ch => φA.expect (C.channel ch D.AD)

/--
Compatibility principle for the model-specific Fierz identity.

This is the only place where the Fierz quadric law is assumed.  Modular fixedness
of the Drazin support alone gives no-leakage, not a Fierz identity.
-/
@[rep_depth operator]
structure HorizonFierzCompatibility
    (Obs : Type*) [Monoid Obs] [Star Obs] [AddCommMonoid Obs] [SMul ℂ Obs] where
  flow : ModularFlow Obs
  compressedState : ExpectationState Obs
  channels : FierzChannelMap Obs
  residual : FierzResidual
  quadric_from_zero_modes :
    ∀ D : DrazinSupportData Obs,
      IsPhysicalHorizon flow D →
      ChannelsAreHorizonZeroModes flow D channels →
        residual.residual (horizonFierzVector compressedState channels D) = 0

/--
If the Drazin support is a modular physical horizon and the Fierz channels are
horizon zero modes, the compressed expectation vector satisfies the supplied
Fierz residual law.
-/
@[rep_depth operator]
theorem fierz_quadric_from_modular_physical_horizon
    {Obs : Type*} [Monoid Obs] [Star Obs] [AddCommMonoid Obs] [SMul ℂ Obs]
    (K : HorizonFierzCompatibility Obs)
    (D : DrazinSupportData Obs)
    (hHorizon : IsPhysicalHorizon K.flow D)
    (hChannels : ChannelsAreHorizonZeroModes K.flow D K.channels) :
    K.residual.residual (horizonFierzVector K.compressedState K.channels D) = 0 :=
  K.quadric_from_zero_modes D hHorizon hChannels

end InfoGeometry.Canonical.DrazinModularPersistence
