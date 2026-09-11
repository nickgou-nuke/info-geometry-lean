import InfoGeometry.Topology.SymbolicLatentObservationQuotientFlowCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeFlowCompHaus

/-!
# Naturality of the observational quotient-range flow

The range flow is the transport of the quotient flow through the canonical
compact-Hausdorff quotient-range isomorphism.  This theorem records that
transport as an equality in `CompHaus`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_eq_conjugatedQuotient
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    Φ.observationQuotientRangeFlowCompHausHom S h_flow t =
      (symbolicObservationQuotientCompHausIso S).inv ≫
        Φ.observationQuotientFlowCompHausHom h_flow t ≫
          (symbolicObservationQuotientCompHausIso S).hom := by
  apply (cancel_epi (symbolicObservationQuotientCompHausIso S).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply ConcreteCategory.hom_ext
  intro q
  change
    (Φ.observationQuotientRangeFlowHomeomorph S h_flow t
      ((symbolicObservationQuotientCompHausIso S).hom q)) =
      (symbolicObservationQuotientCompHausIso S).hom
        (Φ.observationQuotientFlowCompHausHom h_flow t q)
  refine Quotient.inductionOn q ?_
  intro x
  change
    (symbolicObservationQuotientRangeCompactHomeomorph S)
        ((Φ.observationQuotientFlowHomeomorph h_flow t)
          ((symbolicObservationQuotientRangeCompactHomeomorph S).symm
            ((symbolicObservationQuotientRangeCompactHomeomorph S) ⟦x⟧))) =
      (symbolicObservationQuotientRangeCompactHomeomorph S)
        (descendedSymbolicLatentObservationFlow Φ t ⟦x⟧)
  rw [Homeomorph.symm_apply_apply, Φ.observationQuotientFlowHomeomorph_apply h_flow t]
  rfl

end InfoGeometry.Topology
