import InfoGeometry.Topology.SymbolicLatentObservationQuotientOrbitClosureFlowBridge
import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompHaus
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureFlowCompHaus

/-!
# Compact-Hausdorff bridge for observation-quotient orbit closures

The observation quotient is already a `SymbolicLatentFlowQuotient`.  This
owner only exposes the generic compact-Hausdorff orbit-closure transport under
observation-specific names.  No second orbit-closure construction is made.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureCompHaus
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) : CompHaus := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range (X := X) (ι := ι) S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.compactSpace
  letI : T2Space (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.t2Space
  exact symbolicLatentQuotientOrbitClosureCompHaus
    (symbolicLatentObservationQuotientFlow Φ h_cont) q

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowCompHausIso
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ) :
    Φ.observationQuotientOrbitClosureCompHaus h_cont q ≅
    Φ.observationQuotientOrbitClosureCompHaus h_cont
        (descendedSymbolicLatentObservationFlow Φ t q) := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
        (isCompact_symbolicObservationQuotient_range (X := X) (ι := ι) S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.compactSpace
  letI : T2Space (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.t2Space
  dsimp [SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureCompHaus]
  exact (symbolicLatentObservationQuotientFlow Φ h_cont).orbitClosureFlowCompHausIso q t

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowCompHausHom
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ) :
    Φ.observationQuotientOrbitClosureCompHaus h_cont q ⟶
      Φ.observationQuotientOrbitClosureCompHaus h_cont
        (descendedSymbolicLatentObservationFlow Φ t q) :=
  (Φ.observationQuotientOrbitClosureFlowCompHausIso h_cont q t).hom

theorem SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowCompHausHom_isIso
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ) :
    IsIso (Φ.observationQuotientOrbitClosureFlowCompHausHom h_cont q t) :=
  (Φ.observationQuotientOrbitClosureFlowCompHausIso h_cont q t).isIso_hom

end
end InfoGeometry.Topology
