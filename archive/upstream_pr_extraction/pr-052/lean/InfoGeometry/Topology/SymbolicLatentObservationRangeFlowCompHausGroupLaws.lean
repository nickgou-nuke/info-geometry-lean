import InfoGeometry.Topology.SymbolicLatentObservationRangeFlowCompHausComposition

/-!
# Group laws for the CompHaus observational range flow

The zero and inverse laws are lifted from the quotient-flow homeomorphism
construction.  The inverse identities are then consequences of the already
proved CompHaus cocycle.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_zero
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2)) :
    Φ.observationQuotientRangeFlowCompHausHom S h_cont 0 =
      𝟙 (symbolicObservationRangeCompHaus S) := by
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

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_comp_neg
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    Φ.observationQuotientRangeFlowCompHausHom S h_cont t ≫
        Φ.observationQuotientRangeFlowCompHausHom S h_cont (-t) =
      𝟙 (symbolicObservationRangeCompHaus S) := by
  calc
    Φ.observationQuotientRangeFlowCompHausHom S h_cont t ≫
        Φ.observationQuotientRangeFlowCompHausHom S h_cont (-t) =
      Φ.observationQuotientRangeFlowCompHausHom S h_cont ((-t) + t) :=
        Φ.observationQuotientRangeFlowCompHausHom_comp S h_cont t (-t)
    _ = Φ.observationQuotientRangeFlowCompHausHom S h_cont 0 := by
      rw [neg_add_cancel]
    _ = 𝟙 (symbolicObservationRangeCompHaus S) :=
      Φ.observationQuotientRangeFlowCompHausHom_zero S h_cont

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_neg_comp
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    Φ.observationQuotientRangeFlowCompHausHom S h_cont (-t) ≫
        Φ.observationQuotientRangeFlowCompHausHom S h_cont t =
      𝟙 (symbolicObservationRangeCompHaus S) := by
  calc
    Φ.observationQuotientRangeFlowCompHausHom S h_cont (-t) ≫
        Φ.observationQuotientRangeFlowCompHausHom S h_cont t =
      Φ.observationQuotientRangeFlowCompHausHom S h_cont (t + (-t)) :=
        Φ.observationQuotientRangeFlowCompHausHom_comp S h_cont (-t) t
    _ = Φ.observationQuotientRangeFlowCompHausHom S h_cont 0 := by
      rw [add_neg_cancel]
    _ = 𝟙 (symbolicObservationRangeCompHaus S) :=
      Φ.observationQuotientRangeFlowCompHausHom_zero S h_cont

end InfoGeometry.Topology

end
