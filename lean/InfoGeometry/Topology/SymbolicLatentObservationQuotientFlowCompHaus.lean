import InfoGeometry.Topology.SymbolicLatentObservationQuotientReversalCompHaus

/-!
# Compact-Hausdorff flow on the observational quotient

The quotient carrier and its compact-Hausdorff flow map already exist.  This
owner exposes the ordinary modular-flow API under quotient-specific names and
records the group laws in `CompHaus`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    symbolicObservationQuotientCompHaus S ⟶
      symbolicObservationQuotientCompHaus S :=
  Φ.toQuotientCompHausHom h_flow t

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom_forget
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    compHausToTop.map (Φ.observationQuotientFlowCompHausHom h_flow t) =
      Φ.observationQuotientFlowTopCatHom h_flow t :=
  rfl

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom_isIso
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    IsIso (Φ.observationQuotientFlowCompHausHom h_flow t) := by
  have hTopIso : IsIso (Φ.observationQuotientFlowTopCatHom h_flow t) :=
    Φ.observationQuotientFlowTopCatHom_isIso h_flow t
  haveI : IsIso (compHausToTop.map (Φ.observationQuotientFlowCompHausHom h_flow t)) := by
    simpa [SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom_forget]
      using hTopIso
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  exact hFF.isIso_of_isIso_map (Φ.observationQuotientFlowCompHausHom h_flow t)

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom_zero
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2)) :
    Φ.observationQuotientFlowCompHausHom h_flow 0 =
      𝟙 (symbolicObservationQuotientCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro q
  change descendedSymbolicLatentObservationFlow Φ 0 q = q
  exact (symbolicLatentObservationQuotientFlow Φ h_flow).act_zero q

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom_comp
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t s : ℝ) :
    Φ.observationQuotientFlowCompHausHom h_flow t ≫
        Φ.observationQuotientFlowCompHausHom h_flow s =
      Φ.observationQuotientFlowCompHausHom h_flow (t + s) := by
  apply ConcreteCategory.hom_ext
  intro q
  change descendedSymbolicLatentObservationFlow Φ s
      (descendedSymbolicLatentObservationFlow Φ t q) =
    descendedSymbolicLatentObservationFlow Φ (t + s) q
  simpa [add_comm] using
    ((symbolicLatentObservationQuotientFlow Φ h_flow).act_add s t q).symm

theorem SymbolicLatentObservableModularFlow.observationQuotientFlowCompHausHom_comp_neg
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    Φ.observationQuotientFlowCompHausHom h_flow t ≫
        Φ.observationQuotientFlowCompHausHom h_flow (-t) =
      𝟙 (symbolicObservationQuotientCompHaus S) := by
  rw [Φ.observationQuotientFlowCompHausHom_comp h_flow t (-t)]
  simpa using Φ.observationQuotientFlowCompHausHom_zero h_flow

end InfoGeometry.Topology
