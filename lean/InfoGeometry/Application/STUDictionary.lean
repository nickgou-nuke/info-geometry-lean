import InfoGeometry.Applications.STUBlackHoleQubit

/-!
# InfoGeometry/Application/STUDictionary.lean

Concrete constructors for the STU/Qubit dictionary.

This file provides the constructive closure for the dictionary and decoherence
interfaces. It avoids universal existence theorems and instead provides
mechanisms for packaging explicit data and field-specific laws.
-/

namespace InfoGeometry.Application.STUDictionary

open InfoGeometry.Applications.STUQubit

/--
Generic Black-Hole / Qubit dictionary interface.

This structure maps a state space to an invariant carrier space and carries the
specific polynomial equality that makes the invariant readout meaningful.
-/
structure BlackHoleQubitDictionary (J : Type*) where
  embedSTU : ThreeQubitState → J
  quarticInvariant : J → ℝ
  quartic_eq_hyperdeterminant :
    ∀ ψ : ThreeQubitState,
      quarticInvariant (embedSTU ψ) = ThreeQubitState.cayleyHyperdeterminant ψ

namespace BlackHoleQubitDictionary

/-- The polynomial self-model for Cayley's hyperdeterminant. -/
def selfHyperdeterminant :
    BlackHoleQubitDictionary ThreeQubitState where
  embedSTU := id
  quarticInvariant := ThreeQubitState.cayleyHyperdeterminant
  quartic_eq_hyperdeterminant := by
    intro ψ
    rfl

/--
The identity dictionary over the 3-qubit state space.
-/
def identity :
    BlackHoleQubitDictionary ThreeQubitState where
  embedSTU := id
  quarticInvariant := ThreeQubitState.cayleyHyperdeterminant
  quartic_eq_hyperdeterminant := by
    intro ψ
    rfl

@[simp]
theorem selfHyperdeterminant_quartic_eq
    (ψ : ThreeQubitState) :
    identity.quarticInvariant
        (identity.embedSTU ψ)
      =
        ThreeQubitState.cayleyHyperdeterminant ψ :=
  identity.quartic_eq_hyperdeterminant ψ

end BlackHoleQubitDictionary

/-- Generic decoherence-as-Drazin-surgery interface with concrete laws. -/
structure DecoherenceAsDrazinSurgery (State Operator Core : Type*) where
  decoherenceFlow : ℝ → State → State
  drazinProjector : Operator → Operator
  boundaryEvent : State → Prop
  postSurgeryCore : State → Core
  boundary_preserved :
    ∀ (t : ℝ) (state : State),
      boundaryEvent state → boundaryEvent (decoherenceFlow t state)
  projector_idempotent :
    ∀ op : Operator, drazinProjector (drazinProjector op) = drazinProjector op

namespace DecoherenceAsDrazinSurgery

variable {State Operator Core : Type*}

/-- Constructor for explicit decoherence/Drazin-surgery data and its two laws. -/
def ofLaws
    (decoherenceFlow : ℝ → State → State)
    (drazinProjector : Operator → Operator)
    (boundaryEvent : State → Prop)
    (postSurgeryCore : State → Core)
    (boundary_preserved :
      ∀ (t : ℝ) (state : State),
        boundaryEvent state → boundaryEvent (decoherenceFlow t state))
    (projector_idempotent :
      ∀ op : Operator, drazinProjector (drazinProjector op) = drazinProjector op) :
    DecoherenceAsDrazinSurgery State Operator Core where
  decoherenceFlow := decoherenceFlow
  drazinProjector := drazinProjector
  boundaryEvent := boundaryEvent
  postSurgeryCore := postSurgeryCore
  boundary_preserved := boundary_preserved
  projector_idempotent := projector_idempotent

/-- Boundary events remain boundary events under the supplied flow. -/
theorem boundaryEvent_decoherenceFlow
    (D : DecoherenceAsDrazinSurgery State Operator Core)
    (t : ℝ) (state : State)
    (hBoundary : D.boundaryEvent state) :
    D.boundaryEvent (D.decoherenceFlow t state) :=
  D.boundary_preserved t state hBoundary

/-- The supplied Drazin projector is idempotent. -/
theorem drazinProjector_idempotent
    (D : DecoherenceAsDrazinSurgery State Operator Core)
    (op : Operator) :
    D.drazinProjector (D.drazinProjector op) = D.drazinProjector op :=
  D.projector_idempotent op

end DecoherenceAsDrazinSurgery

end InfoGeometry.Application.STUDictionary
