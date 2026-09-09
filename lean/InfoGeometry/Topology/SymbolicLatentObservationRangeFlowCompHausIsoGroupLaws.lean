import InfoGeometry.Topology.SymbolicLatentObservationRangeFlowCompHausGroupLaws

/-!
# Iso-level group laws for the observational range flow

The `CompHaus` flow slices are already constructed as isomorphisms.  This
owner exposes their zero and cocycle laws at the `Iso` level, so later orbit
constructions can use invertible categorical maps directly.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_zero
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2)) :
    Φ.observationQuotientRangeFlowCompHausIso S h_cont 0 =
      Iso.refl (symbolicObservationRangeCompHaus S) := by
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro q
  change Φ.observationQuotientRangeFlowHomeomorph S h_cont 0 q = q
  unfold SymbolicLatentObservableModularFlow.observationQuotientRangeFlowHomeomorph
  change
    (symbolicObservationQuotientRangeCompactHomeomorph S)
        ((symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph 0
          ((symbolicObservationQuotientRangeCompactHomeomorph S).symm q)) = q
  rw [SymbolicLatentFlowQuotient.actHomeomorph_zero_apply]
  exact (symbolicObservationQuotientRangeCompactHomeomorph S).apply_symm_apply q

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_trans
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (s t : ℝ) :
    (Φ.observationQuotientRangeFlowCompHausIso S h_cont s).trans
        (Φ.observationQuotientRangeFlowCompHausIso S h_cont t) =
      Φ.observationQuotientRangeFlowCompHausIso S h_cont (t + s) := by
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro q
  change
    (Φ.observationQuotientRangeFlowHomeomorph S h_cont s).trans
        (Φ.observationQuotientRangeFlowHomeomorph S h_cont t) q =
      Φ.observationQuotientRangeFlowHomeomorph S h_cont (t + s) q
  exact Φ.observationQuotientRangeFlowHomeomorph_comp_apply S h_cont s t q

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_inv_eq_neg_hom
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv =
      (Φ.observationQuotientRangeFlowCompHausIso S h_cont (-t)).hom := by
  apply ConcreteCategory.hom_ext
  intro q
  exact Φ.observationQuotientRangeFlowCompHausIso_inv_apply S h_cont t q

end InfoGeometry.Topology
