import InfoGeometry.Topology.SymbolicLatentFlowQuotientTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeFlowMorphismBridge

/-!
# Canonical quotient property for an observable modular flow

An observable modular flow has exactly the fields required by the existing
`SymbolicLatentFlow` carrier.  This owner packages those fields and proves
that its canonical `flowMorphism` induces the descended quotient action.
-/

noncomputable section

namespace InfoGeometry.Topology

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

def symbolicLatentObservableModularFlowAsFlow
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S) :
    SymbolicLatentFlow S where
  act := Φ.act
  continuous_act := Φ.continuous_act
  zero_apply := Φ.zero_apply
  add_apply := Φ.add_apply
  preserves_observation := Φ.preserves_observation

theorem symbolicLatentObservableModularFlowAsFlow_act
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S) :
    (symbolicLatentObservableModularFlowAsFlow Φ).act = Φ.act :=
  rfl

theorem symbolicLatentObservableModularFlow_flowMorphism_quotientMap_eq
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S) (t : ℝ) (q :
      SymbolicLatentObservationQuotient S) :
    (flowMorphism (symbolicLatentObservableModularFlowAsFlow Φ) t).quotientMap q =
      descendedSymbolicLatentObservationFlow Φ t q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

theorem symbolicObservationRangeCompHausHomOfCanonicalFlowMorphism_eq_flow
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    symbolicObservationRangeCompHausHomOfMorphism
        (flowMorphism (symbolicLatentObservableModularFlowAsFlow Φ) t) =
      Φ.toObservationRangeCompHausHom h_flow t := by
  apply symbolicObservationRangeCompHausHomOfMorphism_eq_flow
  exact symbolicLatentObservableModularFlow_flowMorphism_quotientMap_eq Φ t

end InfoGeometry.Topology
