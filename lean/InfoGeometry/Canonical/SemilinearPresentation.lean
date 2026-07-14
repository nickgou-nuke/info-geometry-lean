import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# InfoGeometry.Canonical.SemilinearPresentation

Proof-rooted semilinear presentation maps.
-/

namespace SemilinearPresentation

/-- Raw module-valued presentation data. -/
@[rep_depth operator]
structure ModulePresentation (R : Type*) [Semiring R] where
  State : Type*
  Observable : Type*
  Readout : Type*

  [stateAdd : AddCommMonoid State]
  [stateModule : Module R State]

  [observableAdd : AddCommMonoid Observable]
  [observableModule : Module R Observable]

  [readoutAdd : AddCommMonoid Readout]
  [readoutModule : Module R Readout]

  act : Observable → State → State
  support : State → Prop
  generator : State →ₗ[R] State
  metricReadout : State →ₗ[R] Readout
  phaseReadout : State →ₗ[R] Readout

attribute [instance]
  ModulePresentation.stateAdd
  ModulePresentation.stateModule
  ModulePresentation.observableAdd
  ModulePresentation.observableModule
  ModulePresentation.readoutAdd
  ModulePresentation.readoutModule

/-- One-way semilinear presentation map over an explicit scalar transport. -/
@[rep_depth krein]
structure SemilinearPresentationMap
    {R S : Type*} [Semiring R] [Semiring S]
    (σ : R →+* S)
    (P : ModulePresentation R)
    (Q : ModulePresentation S) where
  mapState : P.State →ₛₗ[σ] Q.State
  mapObservable : P.Observable →ₛₗ[σ] Q.Observable
  mapReadout : P.Readout →ₛₗ[σ] Q.Readout

  map_act :
    ∀ (o : P.Observable) (s : P.State),
      mapState (P.act o s) = Q.act (mapObservable o) (mapState s)

  map_support :
    ∀ s : P.State, P.support s → Q.support (mapState s)

  map_generator :
    ∀ s : P.State,
      mapState (P.generator s) = Q.generator (mapState s)

  map_metricReadout :
    ∀ s : P.State,
      mapReadout (P.metricReadout s) = Q.metricReadout (mapState s)

  map_phaseReadout :
    ∀ s : P.State,
      mapReadout (P.phaseReadout s) = Q.phaseReadout (mapState s)

/-- Identity semilinear presentation map. -/
@[rep_depth krein]
def idMap
    {R : Type*} [Semiring R]
    (P : ModulePresentation R) :
    SemilinearPresentationMap (RingHom.id R) P P where
  mapState := LinearMap.id
  mapObservable := LinearMap.id
  mapReadout := LinearMap.id
  map_act := by
    intro o s
    rfl
  map_support := by
    intro s hs
    exact hs
  map_generator := by
    intro s
    rfl
  map_metricReadout := by
    intro s
    rfl
  map_phaseReadout := by
    intro s
    rfl

/-- Composition of semilinear presentation maps. -/
@[rep_depth krein]
def compMap
    {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    {σ : R →+* S} {τ : S →+* T}
    {P : ModulePresentation R}
    {Q : ModulePresentation S}
    {U : ModulePresentation T}
    (F : SemilinearPresentationMap σ P Q)
    (G : SemilinearPresentationMap τ Q U) :
    SemilinearPresentationMap (τ.comp σ) P U :=
  letI : RingHomCompTriple σ τ (τ.comp σ) := ⟨rfl⟩
  {
    mapState := G.mapState.comp F.mapState
    mapObservable := G.mapObservable.comp F.mapObservable
    mapReadout := G.mapReadout.comp F.mapReadout
    map_act := by
      intro o s
      calc
        G.mapState (F.mapState (P.act o s))
            = G.mapState (Q.act (F.mapObservable o) (F.mapState s)) := by
                rw [F.map_act o s]
        _ = U.act (G.mapObservable (F.mapObservable o))
            (G.mapState (F.mapState s)) := by
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
        _ = U.generator (G.mapState (F.mapState s)) := by
                rw [G.map_generator (F.mapState s)]
    map_metricReadout := by
      intro s
      calc
        G.mapReadout (F.mapReadout (P.metricReadout s))
            = G.mapReadout (Q.metricReadout (F.mapState s)) := by
                rw [F.map_metricReadout s]
        _ = U.metricReadout (G.mapState (F.mapState s)) := by
                rw [G.map_metricReadout (F.mapState s)]
    map_phaseReadout := by
      intro s
      calc
        G.mapReadout (F.mapReadout (P.phaseReadout s))
            = G.mapReadout (Q.phaseReadout (F.mapState s)) := by
                rw [F.map_phaseReadout s]
        _ = U.phaseReadout (G.mapState (F.mapState s)) := by
                rw [G.map_phaseReadout (F.mapState s)]
  }

/-- Semilinear presentation isomorphism with inverse laws on all transported carriers. -/
@[rep_depth krein]
structure SemilinearPresentationIso
    {R S : Type*} [Semiring R] [Semiring S]
    (σ : R ≃+* S)
    (P : ModulePresentation R)
    (Q : ModulePresentation S) where
  toMap : SemilinearPresentationMap σ.toRingHom P Q
  invMap : SemilinearPresentationMap σ.symm.toRingHom Q P

  left_state :
    ∀ s : P.State, invMap.mapState (toMap.mapState s) = s
  right_state :
    ∀ s : Q.State, toMap.mapState (invMap.mapState s) = s

  left_observable :
    ∀ o : P.Observable, invMap.mapObservable (toMap.mapObservable o) = o
  right_observable :
    ∀ o : Q.Observable, toMap.mapObservable (invMap.mapObservable o) = o

  left_readout :
    ∀ x : P.Readout, invMap.mapReadout (toMap.mapReadout x) = x
  right_readout :
    ∀ x : Q.Readout, toMap.mapReadout (invMap.mapReadout x) = x

/-- Identity semilinear presentation isomorphism. -/
@[rep_depth krein]
def idIso
    {R : Type*} [Semiring R]
    (P : ModulePresentation R) :
    SemilinearPresentationIso (RingEquiv.refl R) P P where
  toMap := idMap P
  invMap := idMap P
  left_state := by
    intro s
    rfl
  right_state := by
    intro s
    rfl
  left_observable := by
    intro o
    rfl
  right_observable := by
    intro o
    rfl
  left_readout := by
    intro x
    rfl
  right_readout := by
    intro x
    rfl

section PairedToy

variable (R : Type*) [CommSemiring R]

/-- Non-vacuous paired toy presentation with diagonal support. -/
@[rep_depth operator]
def pairedPresentation : ModulePresentation R where
  State := R × R
  Observable := R × R
  Readout := R × R
  act := fun o s => (o.1 * s.1, o.2 * s.2)
  support := fun s => s.1 = s.2
  generator :=
    { toFun := fun s => (s.2, s.1)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }
  metricReadout := LinearMap.id
  phaseReadout :=
    { toFun := fun s => (s.2, s.1)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }

/-- Swap map on paired states/readouts. -/
@[rep_depth krein]
def pairedSwapLinear : (R × R) →ₗ[R] (R × R) where
  toFun := fun s => (s.2, s.1)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro r x
    ext <;> simp

/-- The paired swap is a semilinear presentation map. -/
@[rep_depth krein]
def pairedSwapMap :
    SemilinearPresentationMap (RingHom.id R)
      (pairedPresentation R)
      (pairedPresentation R) where
  mapState := pairedSwapLinear R
  mapObservable := pairedSwapLinear R
  mapReadout := pairedSwapLinear R
  map_act := by
    intro o s
    change R × R at o
    change R × R at s
    cases o
    cases s
    rfl
  map_support := by
    intro s hs
    change R × R at s
    change s.1 = s.2 at hs
    change ((pairedSwapLinear R) s).1 = ((pairedSwapLinear R) s).2
    simpa [pairedSwapLinear] using hs.symm
  map_generator := by
    intro s
    change R × R at s
    cases s
    rfl
  map_metricReadout := by
    intro s
    rfl
  map_phaseReadout := by
    intro s
    change R × R at s
    cases s
    rfl

/-- The paired swap is an involutive semilinear presentation isomorphism. -/
@[rep_depth krein]
def pairedSwapIso :
    SemilinearPresentationIso (RingEquiv.refl R)
      (pairedPresentation R)
      (pairedPresentation R) where
  toMap := pairedSwapMap R
  invMap := pairedSwapMap R
  left_state := by
    intro s
    change R × R at s
    cases s
    rfl
  right_state := by
    intro s
    change R × R at s
    cases s
    rfl
  left_observable := by
    intro o
    change R × R at o
    cases o
    rfl
  right_observable := by
    intro o
    change R × R at o
    cases o
    rfl
  left_readout := by
    intro x
    change R × R at x
    cases x
    rfl
  right_readout := by
    intro x
    change R × R at x
    cases x
    rfl

/-- The paired swap is non-identity off the diagonal. -/
@[rep_depth krein]
theorem pairedSwapMap_moves_state
    {a b : R} (h : a ≠ b) :
    (pairedSwapMap R).mapState (a, b) ≠ (a, b) := by
  change (pairedSwapLinear R) (a, b) ≠ (a, b)
  intro hEq
  have hb : b = a := by
    exact congrArg Prod.fst hEq
  exact h hb.symm

end PairedToy

end SemilinearPresentation
