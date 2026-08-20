import InfoGeometry.Canonical.RelativeModularPotentialExactCocycle

/-!
# Observable coordinates over the projective quantum base

This file records the finite, theorem-safe bundle interface used by the
quantum-algebra geometry lane. The base is the existing positive-ray space;
observable coordinates read into that base, and fibers may depend on the ray.
The relative modular potential is the existing exact transition function over
this base. No manifold, homogeneous-space, or de Rham structure is asserted.
-/

namespace InfoGeometry.Canonical.QuantumAlgebraObservableBase

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularPotentialExactCocycle

section

variable {n : ℕ} [Nonempty (Fin n)]

/-- A dependent quantum-algebra fiber assignment over the projective positive base. -/
structure QuantumAlgebraBundleBase (Observable : Type*) where
  coordinate : Observable → PositiveRay (Fin n)
  fiber : PositiveRay (Fin n) → Type*

/-! State-dependent coordinate readouts are kept separate from the static
bundle presentation. A later analytic owner may instantiate these readouts
with Hilbert-space expectation values. -/
structure ExpectationCoordinateData (State Observable : Type*) where
  coordinate : State → Observable → PositiveRay (Fin n)
  fiber : PositiveRay (Fin n) → Type*

namespace ExpectationCoordinateData

variable {State Observable : Type*}
  (E : ExpectationCoordinateData (n := n) State Observable)

def basePoint (ψ : State) (X : Observable) : PositiveRay (Fin n) :=
  E.coordinate ψ X

def fiberAt (ψ : State) (X : Observable) : Type* :=
  E.fiber (E.basePoint ψ X)

@[simp] theorem basePoint_def (ψ : State) (X : Observable) :
    E.basePoint ψ X = E.coordinate ψ X :=
  rfl

end ExpectationCoordinateData

namespace QuantumAlgebraBundleBase

variable {Observable : Type*} (B : QuantumAlgebraBundleBase (n := n) Observable)

/-- The projective base point read out by an observable coordinate. -/
def basePoint (o : Observable) : PositiveRay (Fin n) :=
  B.coordinate o

/-- The quantum-algebra fiber over the base point selected by an observable. -/
def observableFiber (o : Observable) : Type* :=
  B.fiber (B.basePoint o)

/-- The relative modular transition potential between two observable readouts. -/
noncomputable def transitionPotential (o₀ o₁ : Observable) : ℝ :=
  anchoredPotential (n := n) (B.basePoint o₀) (B.basePoint o₁)

/-- The anchored modular potential pulled back to observable coordinates. -/
noncomputable def potentialField (base : PositiveRay (Fin n)) (o : Observable) : ℝ :=
  anchoredPotential (n := n) base (B.basePoint o)

theorem transitionPotential_self (o : Observable) :
    B.transitionPotential o o = 0 := by
  simpa [transitionPotential, anchoredPotential, basePoint] using
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularVolumePotential_self
      (n := n) (B.basePoint o)

theorem transitionPotential_antisymm (o₀ o₁ : Observable) :
    B.transitionPotential o₁ o₀ = -B.transitionPotential o₀ o₁ := by
  simpa [transitionPotential, anchoredPotential, basePoint] using
    InfoGeometry.Canonical.RelativeModularPotentialExactCocycle.relativeModularVolumePotential_antisymm
      (n := n) (B.basePoint o₀) (B.basePoint o₁)

theorem transitionPotential_closed_loop (o₀ o₁ : Observable) :
    B.transitionPotential o₀ o₁ + B.transitionPotential o₁ o₀ = 0 := by
  simpa [transitionPotential, anchoredPotential, basePoint] using
    InfoGeometry.Canonical.RelativeModularPotentialExactCocycle.relativeModularVolumePotential_closed_loop
      (n := n) (B.basePoint o₀) (B.basePoint o₁)

theorem transitionPotential_transitive (o₀ o₁ o₂ : Observable) :
    B.transitionPotential o₀ o₂ =
      B.transitionPotential o₀ o₁ + B.transitionPotential o₁ o₂ := by
  simpa [transitionPotential, anchoredPotential, basePoint] using
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularVolumePotential_cocycle
      (n := n) (B.basePoint o₀) (B.basePoint o₁) (B.basePoint o₂)

theorem transitionPotential_eq_baseDifference
    (o₀ o₁ : Observable) :
    B.transitionPotential o₀ o₁ =
      anchoredPotential (n := n) (B.basePoint o₀) (B.basePoint o₁) :=
  rfl

theorem transitionPotential_eq_potentialField_difference
    (base : PositiveRay (Fin n)) (o₀ o₁ : Observable) :
    B.transitionPotential o₀ o₁ =
      B.potentialField base o₁ - B.potentialField base o₀ := by
  simpa [transitionPotential, potentialField, basePoint] using
    (transition_eq_anchoredPotential_sub
      (n := n) base (B.basePoint o₀) (B.basePoint o₁))

end QuantumAlgebraBundleBase

end

end InfoGeometry.Canonical.QuantumAlgebraObservableBase
