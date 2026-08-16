import Mathlib
import InfoGeometry.Physics.Algebra.TripotentInvariantCarrierBridge

/-!
# Common invariant packet on a tripotent zero-mode carrier

This file packages the exact finite algebraic statement needed before one may
place braid, parabolic, Hodge, and modular readouts on a common horizon
carrier.  The carrier is `ker T = range (1 - T²)` for a tripotent endomorphism
`T`.  Each action is required explicitly to commute with the zero projector;
no braid, protection, Tomita, or analytic claim is smuggled in.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A finite operator packet sharing one tripotent zero-mode carrier. -/
structure HorizonInvariantPacket (V : Type*) [AddCommGroup V] [Module ℝ V] where
  T : Module.End ℝ V
  tripotent : T ^ 3 = T
  braid₁ : Module.End ℝ V
  braid₂ : Module.End ℝ V
  parabolic : Module.End ℝ V
  hodge : Module.End ℝ V
  modular : ℝ → Module.End ℝ V
  braid₁_commutes_zero : braid₁ * endProjZero T = endProjZero T * braid₁
  braid₂_commutes_zero : braid₂ * endProjZero T = endProjZero T * braid₂
  parabolic_commutes_zero : parabolic * endProjZero T = endProjZero T * parabolic
  hodge_commutes_zero : hodge * endProjZero T = endProjZero T * hodge
  modular_commutes_zero : ∀ t, modular t * endProjZero T = endProjZero T * modular t

abbrev HorizonCarrier (P : HorizonInvariantPacket V) : Submodule ℝ V :=
  zeroModeCarrier P.T

abbrev HorizonEnd (P : HorizonInvariantPacket V) :=
  Module.End ℝ (HorizonCarrier P)

theorem horizonCarrier_eq_projector_range (P : HorizonInvariantPacket V) :
    HorizonCarrier P = LinearMap.range (endProjZero P.T) := by
  exact zeroModeCarrier_eq_range_endProjZero P.T P.tripotent

theorem braid₁_preserves_horizon (P : HorizonInvariantPacket V) :
    ∀ x, x ∈ HorizonCarrier P → P.braid₁ x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.braid₁ P.tripotent
    P.braid₁_commutes_zero

theorem braid₂_preserves_horizon (P : HorizonInvariantPacket V) :
    ∀ x, x ∈ HorizonCarrier P → P.braid₂ x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.braid₂ P.tripotent
    P.braid₂_commutes_zero

theorem parabolic_preserves_horizon (P : HorizonInvariantPacket V) :
    ∀ x, x ∈ HorizonCarrier P → P.parabolic x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.parabolic P.tripotent
    P.parabolic_commutes_zero

theorem hodge_preserves_horizon (P : HorizonInvariantPacket V) :
    ∀ x, x ∈ HorizonCarrier P → P.hodge x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.hodge P.tripotent
    P.hodge_commutes_zero

theorem modular_preserves_horizon (P : HorizonInvariantPacket V) (t : ℝ) :
    ∀ x, x ∈ HorizonCarrier P → P.modular t x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T (P.modular t) P.tripotent
    (P.modular_commutes_zero t)

/-- Canonical restriction of an invariant endomorphism to the horizon zero-mode carrier. -/
def restrictToHorizon (P : HorizonInvariantPacket V) (A : Module.End ℝ V)
    (hA : ∀ x, x ∈ HorizonCarrier P → A x ∈ HorizonCarrier P) : HorizonEnd P :=
  LinearMap.restrict A hA

def restrictBraid₁ (P : HorizonInvariantPacket V) : HorizonEnd P :=
  restrictToHorizon P P.braid₁ (braid₁_preserves_horizon P)

def restrictBraid₂ (P : HorizonInvariantPacket V) : HorizonEnd P :=
  restrictToHorizon P P.braid₂ (braid₂_preserves_horizon P)

def restrictParabolic (P : HorizonInvariantPacket V) : HorizonEnd P :=
  restrictToHorizon P P.parabolic (parabolic_preserves_horizon P)

def restrictHodge (P : HorizonInvariantPacket V) : HorizonEnd P :=
  restrictToHorizon P P.hodge (hodge_preserves_horizon P)

def restrictModular (P : HorizonInvariantPacket V) (t : ℝ) : HorizonEnd P :=
  restrictToHorizon P (P.modular t) (modular_preserves_horizon P t)

/-- The composition of restricted operators is the restriction of their composition. -/
theorem restrict_mul (P : HorizonInvariantPacket V) (A B : Module.End ℝ V)
    (hA : ∀ x, x ∈ HorizonCarrier P → A x ∈ HorizonCarrier P)
    (hB : ∀ x, x ∈ HorizonCarrier P → B x ∈ HorizonCarrier P)
    (hAB : ∀ x, x ∈ HorizonCarrier P → (A * B) x ∈ HorizonCarrier P) :
    restrictToHorizon P (A * B) hAB =
      restrictToHorizon P A hA * restrictToHorizon P B hB := by
  ext ⟨x, hx⟩
  rfl

/-- If two ambient endomorphisms commute with `P₀`, their product has the
canonical restricted action on the horizon carrier.  The product-preservation
witness is derived by the generic tripotent commutant theorem. -/
theorem restrict_mul_of_zero_commuting
    (P : HorizonInvariantPacket V) (A B : Module.End ℝ V)
    (hA : A * endProjZero P.T = endProjZero P.T * A)
    (hB : B * endProjZero P.T = endProjZero P.T * B) :
    restrictToHorizon P (A * B)
        (endomorphism_preserves_zeroModeCarrier P.T (A * B) P.tripotent
          (commute_endProjZero_mul P.T A B hA hB)) =
      restrictToHorizon P A
        (endomorphism_preserves_zeroModeCarrier P.T A P.tripotent hA) *
        restrictToHorizon P B
          (endomorphism_preserves_zeroModeCarrier P.T B P.tripotent hB) := by
  apply restrict_mul P A B
    (endomorphism_preserves_zeroModeCarrier P.T A P.tripotent hA)
    (endomorphism_preserves_zeroModeCarrier P.T B P.tripotent hB)

/-- If two commuting operators act non-commutatively on a horizon element, their horizon restrictions do not commute. -/
theorem noncommuting_on_horizon {P : HorizonInvariantPacket V}
    (x : HorizonCarrier P)
    (h_ne : (P.braid₁ * P.braid₂) (x : V) ≠ (P.braid₂ * P.braid₁) (x : V)) :
    restrictBraid₁ P * restrictBraid₂ P ≠ restrictBraid₂ P * restrictBraid₁ P := by
  intro h_eq
  have h_val := congrFun (congrArg (fun (f : HorizonEnd P) => fun (y : HorizonCarrier P) => (f y : V)) h_eq) x
  dsimp [restrictBraid₁, restrictBraid₂, restrictToHorizon, LinearMap.restrict] at h_val
  exact h_ne h_val

end InfoGeometry.Physics.Algebra
