import InfoGeometry.Applications.STUBlackHoleQubit

/-!
# InfoGeometry/Application/STUDictionary.lean

Tautological and proof-carrying constructors for the STU/Qubit dictionary.

This file provides the constructive closure for the dictionary and decoherence
interfaces. It avoids universal existence theorems and instead provides
mechanisms for packaging explicit data and proofs.
-/

namespace InfoGeometry.Application.STUDictionary

open InfoGeometry.Applications.STUQubit

/--
Generic Black-Hole / Qubit dictionary interface.

This is a proof-carrying structure that maps a state space to an invariant
carrier space.
-/
structure BlackHoleQubitDictionary (J : Type*) where
  embedSTU : ThreeQubitState → J
  quarticInvariant : J → ℝ
  quartic_eq_hyperdeterminant :
    ∀ ψ : ThreeQubitState,
      quarticInvariant (embedSTU ψ) = ThreeQubitState.cayleyHyperdeterminant ψ

namespace BlackHoleQubitDictionary

/--
The tautological polynomial dictionary for Cayley's hyperdeterminant.

This is not the black-hole/Freudenthal dictionary. It is a constructive
self-model showing that the dictionary interface is proof-carrying rather than
axiomatic.
-/
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

/--
Generic Decoherence as Drazin Surgery witness.
-/
structure DecoherenceAsDrazinSurgery (State Operator Core : Type*) where
  decoherenceFlow : ℝ → State → State
  drazinProjector : Operator → Operator
  boundaryEvent : State → Prop
  postSurgeryCore : State → Core
  compatibilityStatement : Prop
  compatibilityWitness : compatibilityStatement

namespace DecoherenceAsDrazinSurgery

variable {State Operator Core : Type*}

/--
Constructor wrapper for a proof-carrying decoherence/Drazin-surgery contract.

This does not synthesize a quantum channel, boundary theory, or Drazin model.
It packages supplied data and a supplied compatibility proof.
-/
def ofProof
    (decoherenceFlow : ℝ → State → State)
    (drazinProjector : Operator → Operator)
    (boundaryEvent : State → Prop)
    (postSurgeryCore : State → Core)
    (compatibilityStatement : Prop)
    (compatibilityWitness : compatibilityStatement) :
    DecoherenceAsDrazinSurgery State Operator Core where
  decoherenceFlow := decoherenceFlow
  drazinProjector := drazinProjector
  boundaryEvent := boundaryEvent
  postSurgeryCore := postSurgeryCore
  compatibilityStatement := compatibilityStatement
  compatibilityWitness := compatibilityWitness

/-- The stored compatibility theorem for a supplied model. -/
theorem compatibility
    (D : DecoherenceAsDrazinSurgery State Operator Core) :
    D.compatibilityStatement :=
  D.compatibilityWitness

end DecoherenceAsDrazinSurgery

end InfoGeometry.Application.STUDictionary
