import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHausNaturality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeReversalCompHaus

/-!
# Conditional morphism bridge for observation-range flow

An observation-preserving modular flow supplies a quotient-side action.  This
owner identifies that action with a symbolic morphism only under an explicit
pointwise equality of quotient maps.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem symbolicObservationQuotientCompHausHomOfMorphism_eq_flow
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (F : SymbolicLatentMorphism S S)
    (hF : ∀ q, F.quotientMap q =
      descendedSymbolicLatentObservationFlow Φ t q) :
    symbolicObservationQuotientCompHausHomOfMorphism F =
      Φ.toQuotientCompHausHom h_flow t := by
  apply ConcreteCategory.hom_ext
  intro q
  rw [symbolicObservationQuotientCompHausHomOfMorphism_apply]
  change F.quotientMap q =
    descendedSymbolicLatentObservationFlow Φ t q
  exact hF q

theorem symbolicObservationRangeCompHausHomOfMorphism_eq_flow
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (F : SymbolicLatentMorphism S S)
    (hF : ∀ q, F.quotientMap q =
      descendedSymbolicLatentObservationFlow Φ t q) :
    symbolicObservationRangeCompHausHomOfMorphism F =
      Φ.toObservationRangeCompHausHom h_flow t := by
  rw [symbolicObservationRangeCompHausHomOfMorphism_eq_conjugatedQuotient]
  simp only [SymbolicLatentObservableModularFlow.toObservationRangeCompHausHom]
  rw [symbolicObservationQuotientCompHausHomOfMorphism_eq_flow Φ h_flow t F hF]

end InfoGeometry.Topology
