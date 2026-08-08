import Mathlib
import InfoGeometry.Topology.SymbolicLatentFlowQuotient
import InfoGeometry.Topology.SymbolicLatentModularObservation

namespace InfoGeometry.Topology

/-!
The observational quotient of a finite symbolic latent system and the
descended action of an observation-preserving modular flow.  Continuity of the
quotient action is intentionally supplied as a property: it is a genuine
quotient-topology theorem, not a consequence of pointwise descent alone.
-/

def symbolicLatentObservationSetoid
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : Setoid X where
  r x y := S.obs x = S.obs y
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; exact h.symm
    trans := by intro x y z hxy hyz; exact hxy.trans hyz
  }

abbrev SymbolicLatentObservationQuotient
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :=
  Quotient (symbolicLatentObservationSetoid S)

def symbolicLatentObservationQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    X → SymbolicLatentObservationQuotient S :=
  Quotient.mk _

theorem symbolicLatentObservationQuotientMap_surjective
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Function.Surjective (symbolicLatentObservationQuotientMap S) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

def descendedSymbolicLatentObservationFlow
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S) (t : ℝ) :
    SymbolicLatentObservationQuotient S →
      SymbolicLatentObservationQuotient S :=
  Quotient.lift
    (fun x => symbolicLatentObservationQuotientMap S (Φ.act t x))
    (by
      intro x y hxy
      apply Quotient.sound
      change S.obs (Φ.act t x) = S.obs (Φ.act t y)
      change S.obs x = S.obs y at hxy
      rw [Φ.preserves_observation t x, Φ.preserves_observation t y, hxy])

theorem descendedSymbolicLatentObservationFlow_mk
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S) (t : ℝ) (x : X) :
    descendedSymbolicLatentObservationFlow Φ t
        (symbolicLatentObservationQuotientMap S x) =
      symbolicLatentObservationQuotientMap S (Φ.act t x) := rfl

def symbolicLatentObservationQuotientFlow
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2)) :
    SymbolicLatentFlowQuotient X (SymbolicLatentObservationQuotient S)
      Φ.toSymbolicLatentModularFlow where
  quotientMap := symbolicLatentObservationQuotientMap S
  quotientMap_surjective := symbolicLatentObservationQuotientMap_surjective S
  act := descendedSymbolicLatentObservationFlow Φ
  continuous_act := h_cont
  descends := by
    intro t x
    exact descendedSymbolicLatentObservationFlow_mk Φ t x

end InfoGeometry.Topology
