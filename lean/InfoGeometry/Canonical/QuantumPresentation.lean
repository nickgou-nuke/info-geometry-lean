import InfoGeometry.Meta.Architecture
import Mathlib.Data.Real.Basic

/-!
# InfoGeometry.Canonical.QuantumPresentation

Typed scaffold for "multiple quantum representations, one invariant package".

This file is a translator/interface surface, not a grand-unification owner.
It packages the minimal invariants that presentation morphisms must respect.
-/

namespace InfoGeometry.Canonical.QuantumPresentation

/-- Named representation lanes tracked in this repository program. -/
@[rep_depth operator]
inductive PresentationLane where
  | wavefunction
  | operator
  | phaseSpace
  | hydrodynamic
  | stochastic
  | graphDirac
  | arnoldNetwork
  | doubledKrein
  deriving DecidableEq, Repr

/--
Minimal invariant package for a quantum presentation.

The point is not to force one ontology, but to require a common typed contract:
state support, observable action, generator lane, and scalar readouts.
-/
@[rep_depth operator]
structure Presentation where
  Scalar : Type
  State : Type
  Observable : Type
  act : Observable → State → State
  support : State → Prop
  generator : State → State
  metricReadout : State → Scalar
  phaseReadout : State → Scalar

/-- Attach lane metadata to a concrete presentation instance. -/
@[rep_depth operator]
structure TaggedPresentation where
  lane : PresentationLane
  data : Presentation

/--
Intertwiner between two presentations.

This is the typed place where "same physics, different representation" lives.
-/
@[rep_depth krein]
structure Intertwiner (P Q : Presentation) where
  mapState : P.State → Q.State
  mapObservable : P.Observable → Q.Observable
  mapScalar : P.Scalar → Q.Scalar
  map_act :
    ∀ (o : P.Observable) (s : P.State),
      mapState (P.act o s) = Q.act (mapObservable o) (mapState s)
  map_support :
    ∀ s, P.support s → Q.support (mapState s)
  map_generator :
    ∀ s, mapState (P.generator s) = Q.generator (mapState s)

/-- Scalar readout preservation contract for an intertwiner. -/
@[rep_depth krein]
structure ReadoutPreservation
    {P Q : Presentation} (F : Intertwiner P Q) : Prop where
  metric :
    ∀ s, F.mapScalar (P.metricReadout s) = Q.metricReadout (F.mapState s)
  phase :
    ∀ s, F.mapScalar (P.phaseReadout s) = Q.phaseReadout (F.mapState s)

/-- Identity intertwiner on a presentation. -/
@[rep_depth krein]
def idIntertwiner (P : Presentation) : Intertwiner P P where
  mapState := fun s => s
  mapObservable := fun o => o
  mapScalar := fun x => x
  map_act := by
    intro o s
    rfl
  map_support := by
    intro s hs
    exact hs
  map_generator := by
    intro s
    rfl

/-- Composition of intertwiners. -/
@[rep_depth krein]
def compIntertwiner
    {P Q R : Presentation}
    (F : Intertwiner P Q)
    (G : Intertwiner Q R) :
    Intertwiner P R where
  mapState := fun s => G.mapState (F.mapState s)
  mapObservable := fun o => G.mapObservable (F.mapObservable o)
  mapScalar := fun x => G.mapScalar (F.mapScalar x)
  map_act := by
    intro o s
    calc
      G.mapState (F.mapState (P.act o s))
          = G.mapState (Q.act (F.mapObservable o) (F.mapState s)) := by
              rw [F.map_act o s]
      _ = R.act (G.mapObservable (F.mapObservable o)) (G.mapState (F.mapState s)) := by
              rw [G.map_act (F.mapObservable o) (F.mapState s)]
  map_support := by
    intro s hs
    exact G.map_support (F.mapState s) (F.map_support s hs)
  map_generator := by
    intro s
    calc
      G.mapState (F.mapState (P.generator s))
          = G.mapState (Q.generator (F.mapState s)) := by
              rw [F.map_generator s]
      _ = R.generator (G.mapState (F.mapState s)) := by
              rw [G.map_generator (F.mapState s)]

/--
Concrete nontrivial presentation on paired states.

This gives a load-bearing witness that the intertwiner lane is not only identity
scaffolding: the state map can be a genuine symmetry (swap) while preserving the
typed action/support/generator contracts.
-/
@[rep_depth operator]
def pairedFunctionPresentation (α : Type) : Presentation where
  Scalar := Nat
  State := α × α
  Observable := α → α
  act := fun o s => (o s.1, o s.2)
  support := fun s => s.1 = s.1
  generator := fun s => (s.2, s.1)
  -- DEBT_ID: QPR_PAIRED_METRIC
  -- DEBT_KIND: ZERO_DATUM
  -- ZERO_DATUM: Trivial metric for paired function model
  metricReadout := fun _ => 0
  -- DEBT_ID: QPR_PAIRED_PHASE
  -- DEBT_KIND: ZERO_DATUM
  -- ZERO_DATUM: Trivial phase for paired function model
  phaseReadout := fun _ => 0

/-- Non-identity symmetry intertwiner on the paired-function presentation. -/
@[rep_depth krein]
def pairedSwapIntertwiner (α : Type) :
    Intertwiner (pairedFunctionPresentation α) (pairedFunctionPresentation α) where
  mapState := fun s => (s.2, s.1)
  mapObservable := fun o => o
  mapScalar := fun x => x
  map_act := by
    intro o s
    cases s
    rfl
  map_support := by
    intro s hs
    trivial
  map_generator := by
    intro s
    cases s
    rfl

/-- Readout preservation for the paired swap intertwiner. -/
@[rep_depth krein]
def pairedSwapReadoutPreservation (α : Type) :
    ReadoutPreservation (pairedSwapIntertwiner α) where
  metric := by
    intro s
    rfl
  phase := by
    intro s
    rfl

@[rep_depth krein]
theorem pairedSwapIntertwiner_moves_state
    {α : Type} (a b : α) (h : a ≠ b) :
    (pairedSwapIntertwiner α).mapState (a, b) ≠ (a, b) := by
  intro hEq
  have hb : b = a := by
    exact congrArg Prod.fst hEq
  exact h hb.symm

end InfoGeometry.Canonical.QuantumPresentation
