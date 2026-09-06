import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompHaus
import InfoGeometry.Topology.SymbolicLatentObservationQuotientReversalTopCat

/-!
# Compact-Hausdorff reversal and flow on observational quotients

The quotient reversal-flow law already exists in `TopCat`.  This owner
packages the same maps in `CompHaus` using the existing compact quotient
carrier; it adds no new compactness or covariance assumptions.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

noncomputable def SymbolicLatentObservableModularReversal.toQuotientCompHausHom
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
    symbolicObservationQuotientCompHaus S ⟶
      symbolicObservationQuotientCompHaus S := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.compactSpace
  letI : T2Space (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.t2Space
  change CompHaus.of (SymbolicLatentObservationQuotient S) ⟶
    CompHaus.of (SymbolicLatentObservationQuotient S)
  exact ⟨R.toQuotientTopCatHom h_cont⟩

noncomputable def SymbolicLatentObservableModularFlow.toQuotientCompHausHom
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    symbolicObservationQuotientCompHaus S ⟶
      symbolicObservationQuotientCompHaus S := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.compactSpace
  letI : T2Space (SymbolicLatentObservationQuotient S) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.t2Space
  change CompHaus.of (SymbolicLatentObservationQuotient S) ⟶
    CompHaus.of (SymbolicLatentObservationQuotient S)
  exact ⟨Φ.observationQuotientFlowTopCatHom h_flow t⟩

theorem SymbolicLatentObservableModularReversal.toQuotientCompHausHom_square
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
    R.toQuotientCompHausHom h_cont ≫
        R.toQuotientCompHausHom h_cont =
      𝟙 (symbolicObservationQuotientCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro q
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply]
  change descendedSymbolicLatentObservationInvolution R
      (descendedSymbolicLatentObservationInvolution R q) = q
  exact descendedSymbolicLatentObservationInvolution_involutive R q

theorem SymbolicLatentObservableModularReversal.toQuotientCompHausHom_flow_reversal
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (t : ℝ) :
    Φ.toQuotientCompHausHom h_flow t ≫
        R.toQuotientCompHausHom h_cont =
      R.toQuotientCompHausHom h_cont ≫
        Φ.toQuotientCompHausHom h_flow (-t) := by
  apply ConcreteCategory.hom_ext
  intro q
  simp only [CategoryTheory.comp_apply]
  change descendedSymbolicLatentObservationInvolution R
      (descendedSymbolicLatentObservationFlow Φ t q) =
    descendedSymbolicLatentObservationFlow Φ (-t)
      (descendedSymbolicLatentObservationInvolution R q)
  exact SymbolicLatentObservableModularReversal.toQuotientInvolution_reverses_flow
    R h_flow h_cont t q

end InfoGeometry.Topology
