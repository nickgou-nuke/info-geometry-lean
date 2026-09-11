import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHausNaturality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeReversalCompHaus

/-!
# Conditional morphism bridge for observation-range reversal

The modular reversal is a quotient-side action.  This owner records the
additional property needed to identify it with a morphism of the original
finite symbolic systems: the induced quotient map must agree pointwise with
the descended reversal.  No reversal morphism is inferred without that
property.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem symbolicObservationQuotientCompHausHomOfMorphism_eq_reversal
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (F : SymbolicLatentMorphism S S)
    (hF : ∀ q, F.quotientMap q =
      descendedSymbolicLatentObservationInvolution R q) :
    symbolicObservationQuotientCompHausHomOfMorphism F =
      R.toQuotientCompHausHom h_cont := by
  apply ConcreteCategory.hom_ext
  intro q
  rw [symbolicObservationQuotientCompHausHomOfMorphism_apply]
  change F.quotientMap q =
    descendedSymbolicLatentObservationInvolution R q
  exact hF q

theorem symbolicObservationRangeCompHausHomOfMorphism_eq_reversal
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (F : SymbolicLatentMorphism S S)
    (hF : ∀ q, F.quotientMap q =
      descendedSymbolicLatentObservationInvolution R q) :
    symbolicObservationRangeCompHausHomOfMorphism F =
      R.toObservationRangeCompHausHom h_cont := by
  rw [symbolicObservationRangeCompHausHomOfMorphism_eq_conjugatedQuotient]
  simp only [SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom]
  rw [symbolicObservationQuotientCompHausHomOfMorphism_eq_reversal R h_cont F hF]

end InfoGeometry.Topology
