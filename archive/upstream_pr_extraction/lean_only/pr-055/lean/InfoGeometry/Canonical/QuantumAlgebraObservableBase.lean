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

/-! A pointwise-positive observable readout is enough to construct a projective
coordinate.  Positivity is explicit because an arbitrary operator expectation
need not define a point of the positive cone. -/
structure PositiveObservableReadout (State Observable : Type*) where
  expectation : State → Observable → Fin n → ℝ
  positive : ∀ ψ X i, 0 < expectation ψ X i

namespace PositiveObservableReadout

variable {State Observable : Type*}
  (R : PositiveObservableReadout (n := n) State Observable)

noncomputable def toExpectationCoordinateData
    (fiber : PositiveRay (Fin n) → Type*) :
    ExpectationCoordinateData (n := n) State Observable where
  coordinate := fun ψ X =>
    Quotient.mk _
      ({ mass := R.expectation ψ X
         pos := fun i => R.positive ψ X i } :
        InfoGeometry.PositiveMeasure (Fin n) ℝ)
  fiber := fiber

omit [Nonempty (Fin n)] in
@[simp] theorem toExpectationCoordinateData_coordinate
    (fiber : PositiveRay (Fin n) → Type*) (ψ : State) (X : Observable) :
    (R.toExpectationCoordinateData fiber).coordinate ψ X =
      Quotient.mk _
        ({ mass := R.expectation ψ X
           pos := fun i => R.positive ψ X i } :
          InfoGeometry.PositiveMeasure (Fin n) ℝ) :=
  rfl

end PositiveObservableReadout

namespace ExpectationCoordinateData

variable {State Observable : Type*}
  (E : ExpectationCoordinateData (n := n) State Observable)

def basePoint (ψ : State) (X : Observable) : PositiveRay (Fin n) :=
  E.coordinate ψ X

def fiberAt (ψ : State) (X : Observable) : Type* :=
  E.fiber (E.basePoint ψ X)

/-! The relative potential pulled back along two observable coordinates of one
state.  The state is part of the pullback data; no identification of the
state space with a smooth manifold is required. -/
noncomputable def transitionPotential
    (ψ : State) (X₀ X₁ : Observable) : ℝ :=
  anchoredPotential (n := n) (E.basePoint ψ X₀) (E.basePoint ψ X₁)

noncomputable def potentialField
    (base : PositiveRay (Fin n)) (ψ : State) (X : Observable) : ℝ :=
  anchoredPotential (n := n) base (E.basePoint ψ X)

theorem transitionPotential_self (ψ : State) (X : Observable) :
    E.transitionPotential ψ X X = 0 := by
  simp [transitionPotential, anchoredPotential]

theorem transitionPotential_antisymm
    (ψ : State) (X₀ X₁ : Observable) :
    E.transitionPotential ψ X₁ X₀ = -E.transitionPotential ψ X₀ X₁ := by
  simpa [transitionPotential, anchoredPotential] using
    InfoGeometry.Canonical.RelativeModularPotentialExactCocycle.relativeModularVolumePotential_antisymm
      (n := n) (E.basePoint ψ X₀) (E.basePoint ψ X₁)

theorem transitionPotential_transitive
    (ψ : State) (X₀ X₁ X₂ : Observable) :
    E.transitionPotential ψ X₀ X₂ =
      E.transitionPotential ψ X₀ X₁ + E.transitionPotential ψ X₁ X₂ := by
  simpa [transitionPotential, anchoredPotential] using
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularVolumePotential_cocycle
      (n := n) (E.basePoint ψ X₀) (E.basePoint ψ X₁) (E.basePoint ψ X₂)

theorem transitionPotential_closed_loop
    (ψ : State) (X₀ X₁ : Observable) :
    E.transitionPotential ψ X₀ X₁ + E.transitionPotential ψ X₁ X₀ = 0 := by
  have h := E.transitionPotential_antisymm ψ X₀ X₁
  linarith

theorem transitionPotential_eq_potentialField_difference
    (base : PositiveRay (Fin n)) (ψ : State) (X₀ X₁ : Observable) :
    E.transitionPotential ψ X₀ X₁ =
      E.potentialField base ψ X₁ - E.potentialField base ψ X₀ := by
  simpa [transitionPotential, potentialField] using
    (transition_eq_anchoredPotential_sub
      (n := n) base (E.basePoint ψ X₀) (E.basePoint ψ X₁))

theorem bundlePotentialField_transport
    (base : PositiveRay (Fin n)) (ψ : State) (X₀ X₁ : Observable) :
    E.potentialField base ψ X₁ =
      E.potentialField base ψ X₀ + E.transitionPotential ψ X₀ X₁ := by
  have h := E.transitionPotential_eq_potentialField_difference base ψ X₀ X₁
  linarith

omit [Nonempty (Fin n)] in
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
  simp [transitionPotential, anchoredPotential, basePoint]

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

theorem potentialField_transport
    (base : PositiveRay (Fin n)) (o₀ o₁ : Observable) :
    B.potentialField base o₁ =
      B.potentialField base o₀ + B.transitionPotential o₀ o₁ := by
  have h := B.transitionPotential_eq_potentialField_difference base o₀ o₁
  linarith

end QuantumAlgebraBundleBase

end

end InfoGeometry.Canonical.QuantumAlgebraObservableBase
