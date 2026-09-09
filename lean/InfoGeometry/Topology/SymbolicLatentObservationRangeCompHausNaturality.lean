import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHausFunctor
import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompHausFunctor

/-!
# Functorial conjugation of quotient and range maps

The natural isomorphism between the observational quotient functor and the
observation-range functor identifies every range morphism with the conjugate
of its quotient morphism.  This is the categorical naturality theorem needed
before specializing any action to a reversal or a flow.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem symbolicObservationRangeCompHausHomOfMorphism_eq_conjugatedQuotient
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicObservationRangeCompHausHomOfMorphism F =
      (symbolicObservationQuotientCompHausIso S).inv ≫
        symbolicObservationQuotientCompHausHomOfMorphism F ≫
          (symbolicObservationQuotientCompHausIso T).hom := by
  apply (cancel_epi (symbolicObservationQuotientCompHausIso S).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (symbolicObservationQuotientRangeCompHausNaturalIso.hom.naturality F).symm

end InfoGeometry.Topology
