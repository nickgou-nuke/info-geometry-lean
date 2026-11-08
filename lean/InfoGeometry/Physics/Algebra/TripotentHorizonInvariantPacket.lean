import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Algebra.TripotentInvariantCarrierBridge

/-!
# Common invariant data on a tripotent zero-mode carrier

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
structure HorizonInvariantData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  T : Module.End ℝ V
  braid₁ : Module.End ℝ V
  braid₂ : Module.End ℝ V
  parabolic : Module.End ℝ V
  hodge : Module.End ℝ V
  modular : ℝ → Module.End ℝ V
def HorizonInvariantLaws (P : HorizonInvariantData V) : Prop :=
  P.T ^ 3 = P.T ∧
  P.braid₁ * endProjZero P.T = endProjZero P.T * P.braid₁ ∧
  P.braid₂ * endProjZero P.T = endProjZero P.T * P.braid₂ ∧
  P.parabolic * endProjZero P.T = endProjZero P.T * P.parabolic ∧
  P.hodge * endProjZero P.T = endProjZero P.T * P.hodge ∧
  (∀ t, P.modular t * endProjZero P.T = endProjZero P.T * P.modular t)

abbrev HorizonCarrier (P : HorizonInvariantData V) : Submodule ℝ V :=
  zeroModeCarrier P.T

abbrev HorizonEnd (P : HorizonInvariantData V) :=
  Module.End ℝ (HorizonCarrier P)

theorem horizonCarrier_eq_projector_range (P : HorizonInvariantData V)
    (hP : HorizonInvariantLaws P) :
    HorizonCarrier P = LinearMap.range (endProjZero P.T) := by
  exact zeroModeCarrier_eq_range_endProjZero P.T hP.1

theorem braid₁_preserves_horizon (P : HorizonInvariantData V)
    (hP : HorizonInvariantLaws P) :
    ∀ x, x ∈ HorizonCarrier P → P.braid₁ x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.braid₁ hP.1 hP.2.1

theorem braid₂_preserves_horizon (P : HorizonInvariantData V)
    (hP : HorizonInvariantLaws P) :
    ∀ x, x ∈ HorizonCarrier P → P.braid₂ x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.braid₂ hP.1 hP.2.2.1

theorem parabolic_preserves_horizon (P : HorizonInvariantData V)
    (hP : HorizonInvariantLaws P) :
    ∀ x, x ∈ HorizonCarrier P → P.parabolic x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.parabolic hP.1 hP.2.2.2.1

theorem hodge_preserves_horizon (P : HorizonInvariantData V)
    (hP : HorizonInvariantLaws P) :
    ∀ x, x ∈ HorizonCarrier P → P.hodge x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T P.hodge hP.1 hP.2.2.2.2.1

theorem modular_preserves_horizon (P : HorizonInvariantData V)
    (hP : HorizonInvariantLaws P) (t : ℝ) :
    ∀ x, x ∈ HorizonCarrier P → P.modular t x ∈ HorizonCarrier P := by
  exact endomorphism_preserves_zeroModeCarrier P.T (P.modular t) hP.1
    (hP.2.2.2.2.2 t)

/-- Canonical restriction of an invariant endomorphism to the horizon zero-mode carrier. -/
def restrictToHorizon (P : HorizonInvariantData V) (A : Module.End ℝ V)
    (hA : ∀ x, x ∈ HorizonCarrier P → A x ∈ HorizonCarrier P) : HorizonEnd P :=
  LinearMap.restrict A hA

def restrictBraid₁ (P : HorizonInvariantData V) (hP : HorizonInvariantLaws P) : HorizonEnd P :=
  restrictToHorizon P P.braid₁ (braid₁_preserves_horizon P hP)

def restrictBraid₂ (P : HorizonInvariantData V) (hP : HorizonInvariantLaws P) : HorizonEnd P :=
  restrictToHorizon P P.braid₂ (braid₂_preserves_horizon P hP)

def restrictParabolic (P : HorizonInvariantData V) (hP : HorizonInvariantLaws P) : HorizonEnd P :=
  restrictToHorizon P P.parabolic (parabolic_preserves_horizon P hP)

def restrictHodge (P : HorizonInvariantData V) (hP : HorizonInvariantLaws P) : HorizonEnd P :=
  restrictToHorizon P P.hodge (hodge_preserves_horizon P hP)

def restrictModular (P : HorizonInvariantData V) (hP : HorizonInvariantLaws P) (t : ℝ) : HorizonEnd P :=
  restrictToHorizon P (P.modular t) (modular_preserves_horizon P hP t)

/-- The composition of restricted operators is the restriction of their composition. -/
theorem restrict_mul (P : HorizonInvariantData V) (A B : Module.End ℝ V)
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
    (P : HorizonInvariantData V) (hP : HorizonInvariantLaws P)
    (A B : Module.End ℝ V)
    (hA : A * endProjZero P.T = endProjZero P.T * A)
    (hB : B * endProjZero P.T = endProjZero P.T * B) :
    restrictToHorizon P (A * B)
        (endomorphism_preserves_zeroModeCarrier P.T (A * B) hP.1
          (commute_endProjZero_mul P.T A B hA hB)) =
      restrictToHorizon P A
        (endomorphism_preserves_zeroModeCarrier P.T A hP.1 hA) *
        restrictToHorizon P B
          (endomorphism_preserves_zeroModeCarrier P.T B hP.1 hB) := by
  apply restrict_mul P A B
    (endomorphism_preserves_zeroModeCarrier P.T A hP.1 hA)
    (endomorphism_preserves_zeroModeCarrier P.T B hP.1 hB)

/-- If two commuting operators act non-commutatively on a horizon element, their horizon restrictions do not commute. -/
theorem noncommuting_on_horizon {P : HorizonInvariantData V}
    (hP : HorizonInvariantLaws P) (x : HorizonCarrier P)
    (h_ne : (P.braid₁ * P.braid₂) (x : V) ≠ (P.braid₂ * P.braid₁) (x : V)) :
    restrictBraid₁ P hP * restrictBraid₂ P hP ≠
      restrictBraid₂ P hP * restrictBraid₁ P hP := by
  intro h_eq
  have h_val := congrFun (congrArg (fun (f : HorizonEnd P) => fun (y : HorizonCarrier P) => (f y : V)) h_eq) x
  dsimp [restrictBraid₁, restrictBraid₂, restrictToHorizon, LinearMap.restrict] at h_val
  exact h_ne h_val

end InfoGeometry.Physics.Algebra
