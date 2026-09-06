/-
InfoGeometry/Thermo/BuresWassersteinKMSCost.lean

Bures-Wasserstein cost of KMS/Wilson holonomy transport.

This module records the metric-cost layer:

  KMS / modular data
    → holonomy transport of positive states
    → Bures-Wasserstein distance/cost between original and transported states.

It does not claim that KMS analyticity alone constructs the Bures-Wasserstein
metric.  The positive-state domain and metric are supplied as proof-carrying
data.
-/

import Mathlib
import InfoGeometry.Geometry.BilingualAnalyticity

noncomputable section

namespace InfoGeometry.Thermo.BuresWassersteinKMSCost

open InfoGeometry.Geometry.BilingualAnalyticity

/-! ## 1. Positive state domain -/

/--
A positive-state domain.

`State` may later be instantiated by density matrices, positive trace-class
operators, weights, or a finite-dimensional positive cone.
-/
structure PositiveStateDomain
    (State : Type*) where
  carrier : Set State

/-- A point of a positive-state domain. -/
structure PositiveState
    {State : Type*}
    (Ω : PositiveStateDomain State) where
  val : State
  mem : val ∈ Ω.carrier

namespace PositiveState

variable {State : Type*} {Ω : PositiveStateDomain State}

instance : CoeOut (PositiveState Ω) State where
  coe ρ := ρ.val

@[simp]
theorem coe_mk
    (x : State)
    (hx : x ∈ Ω.carrier) :
    ((PositiveState.mk x hx : PositiveState Ω) : State) = x :=
  rfl

/-- Positive states are equal when their underlying states are equal. -/
@[ext]
theorem ext
    {ρ σ : PositiveState Ω}
    (h : ρ.val = σ.val) :
    ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

end PositiveState

/-! ## 2. Bures-Wasserstein metric datum -/

/--
Bures-Wasserstein metric/cost datum.

For finite-dimensional positive matrices, a concrete model may instantiate
`squaredDist` by the usual Bures-Wasserstein formula.  This file keeps the
metric backend abstract.
-/
structure BuresWassersteinDatum
    (State : Type*)
    (Ω : PositiveStateDomain State) where
  /-- Distance. -/
  dist : PositiveState Ω → PositiveState Ω → ℝ

  /-- Squared distance/cost. -/
  squaredDist : PositiveState Ω → PositiveState Ω → ℝ

  /-- Nonnegativity of the distance. -/
  dist_nonneg :
    ∀ ρ σ : PositiveState Ω, 0 ≤ dist ρ σ

  /-- Nonnegativity of the squared cost. -/
  squaredDist_nonneg :
    ∀ ρ σ : PositiveState Ω, 0 ≤ squaredDist ρ σ

  /-- Distance vanishes on the diagonal. -/
  dist_self :
    ∀ ρ : PositiveState Ω, dist ρ ρ = 0

  /-- Squared cost vanishes on the diagonal. -/
  squaredDist_self :
    ∀ ρ : PositiveState Ω, squaredDist ρ ρ = 0


namespace BuresWassersteinDatum

variable {State : Type*} {Ω : PositiveStateDomain State}
variable (BW : BuresWassersteinDatum State Ω)

/-- Squared Bures-Wasserstein cost is nonnegative. -/
theorem cost_nonneg
    (ρ σ : PositiveState Ω) :
    0 ≤ BW.squaredDist ρ σ :=
  BW.squaredDist_nonneg ρ σ

/-- Squared Bures-Wasserstein cost vanishes on the diagonal. -/
theorem cost_self
    (ρ : PositiveState Ω) :
    BW.squaredDist ρ ρ = 0 :=
  BW.squaredDist_self ρ

end BuresWassersteinDatum

/-! ## 3. Modular/KMS holonomy transport -/

/--
A KMS/Wilson holonomy transport on positive states.

This is the metric-facing version of the thermal Wilson loop:

`ρ ↦ Hol(ρ)`.

Concrete models may obtain it from modular flow, Wilson holonomy, parallel
transport, or a thermal cylinder analytic continuation.
-/
structure KMSHolonomyTransport
    (State : Type*)
    (Ω : PositiveStateDomain State) where
  /-- Holonomy/transport of a positive state. -/
  transport : State → State

  /-- Transport preserves the positive-state domain. -/
  preserves_domain :
    ∀ ρ : State, ρ ∈ Ω.carrier → transport ρ ∈ Ω.carrier


namespace KMSHolonomyTransport

variable {State : Type*} {Ω : PositiveStateDomain State}
variable (H : KMSHolonomyTransport State Ω)

/-- Transported positive state. -/
def transported
    (ρ : PositiveState Ω) : PositiveState Ω where
  val := H.transport ρ.val
  mem := H.preserves_domain ρ.val ρ.mem

end KMSHolonomyTransport

/-! ## 4. Bures-Wasserstein holonomy cost -/

/-- Bures-Wasserstein cost of a KMS/Wilson holonomy transition. -/
def holonomyCost
    {State : Type*}
    {Ω : PositiveStateDomain State}
    (BW : BuresWassersteinDatum State Ω)
    (H : KMSHolonomyTransport State Ω)
    (ρ : PositiveState Ω) : ℝ :=
  BW.squaredDist ρ (H.transported ρ)

/-- Bures-Wasserstein holonomy cost is nonnegative. -/
theorem holonomyCost_nonneg
    {State : Type*}
    {Ω : PositiveStateDomain State}
    (BW : BuresWassersteinDatum State Ω)
    (H : KMSHolonomyTransport State Ω)
    (ρ : PositiveState Ω) :
    0 ≤ holonomyCost BW H ρ :=
  BW.squaredDist_nonneg ρ (H.transported ρ)

/--
If the holonomy fixes the state, the Bures-Wasserstein holonomy cost vanishes.
-/
theorem holonomyCost_eq_zero_of_fixed
    {State : Type*}
    {Ω : PositiveStateDomain State}
    (BW : BuresWassersteinDatum State Ω)
    (H : KMSHolonomyTransport State Ω)
    (ρ : PositiveState Ω)
    (hfixed : H.transport ρ.val = ρ.val) :
    holonomyCost BW H ρ = 0 := by
  have hstate :
      H.transported ρ = ρ := by
    apply PositiveState.ext
    exact hfixed
  rw [holonomyCost, hstate]
  exact BW.squaredDist_self ρ

/-! ## 5. Detailed balance as zero holonomy cost -/

/--
Detailed balance / reversibility interpreted through the Bures-Wasserstein cost.

This is a bridge datum.  It says that the chosen notion of detailed balance is
equivalent to vanishing Bures-Wasserstein holonomy cost.
-/
structure BuresDetailedBalanceBridge
    (State : Type*)
    (Ω : PositiveStateDomain State)
    (BW : BuresWassersteinDatum State Ω)
    (H : KMSHolonomyTransport State Ω) where

  /-- Detailed balance predicate on positive states. -/
  DetailedBalanced : PositiveState Ω → Prop

  /-- Detailed balance implies zero holonomy cost. -/
  detailed_balance_implies_zero_cost :
    ∀ ρ : PositiveState Ω,
      DetailedBalanced ρ →
        holonomyCost BW H ρ = 0

  /-- Converse: zero cost implies detailed balance. -/
  zero_cost_implies_detailed_balance :
    ∀ ρ : PositiveState Ω,
      holonomyCost BW H ρ = 0 →
        DetailedBalanced ρ

namespace BuresDetailedBalanceBridge

variable
    {State : Type*}
    {Ω : PositiveStateDomain State}
    {BW : BuresWassersteinDatum State Ω}
    {H : KMSHolonomyTransport State Ω}

variable (B : BuresDetailedBalanceBridge State Ω BW H)

/-- Detailed-balanced states have zero Bures-Wasserstein holonomy cost. -/
theorem cost_zero_of_detailed_balance
    {ρ : PositiveState Ω}
    (hρ : B.DetailedBalanced ρ) :
    holonomyCost BW H ρ = 0 :=
  B.detailed_balance_implies_zero_cost ρ hρ

/-- Zero Bures-Wasserstein holonomy cost gives detailed balance. -/
theorem detailed_balance_of_cost_zero
    {ρ : PositiveState Ω}
    (hρ : holonomyCost BW H ρ = 0) :
    B.DetailedBalanced ρ :=
  B.zero_cost_implies_detailed_balance ρ hρ

end BuresDetailedBalanceBridge

/-! ## 6. KMS/Bilingual analyticity compatibility socket -/

/--
Compatibility between bilingual analyticity and KMS/Wilson holonomy transport.

This is where one installs the theorem that a closed bilingual analytic form
around the thermal cylinder produces the holonomy transport used above.
-/
structure BilingualKMSHolonomyCompatibility
    (State Region Point Tangent Value : Type*)
    [AddCommGroup Value] [Module ℝ Value]
    (Ω : PositiveStateDomain State)
    (I : GeometricIntegralBackend Region Point Tangent Value) where

  /-- KMS/Wilson holonomy transport. -/
  holonomy :
    KMSHolonomyTransport State Ω

  /-- Bilingual/Stokes analytic origin of the holonomy transport. -/
  bilingual_stokes_holonomy : Prop

  /-- Thermal-cylinder / KMS-strip interpretation. -/
  thermal_cylinder : Prop

namespace BilingualKMSHolonomyCompatibility

variable
    {State Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {Ω : PositiveStateDomain State}
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (C : BilingualKMSHolonomyCompatibility State Region Point Tangent Value Ω I)

end BilingualKMSHolonomyCompatibility

end InfoGeometry.Thermo.BuresWassersteinKMSCost
