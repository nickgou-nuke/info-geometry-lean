import InfoGeometry.Topology.SymbolicLatentObservationQuotientTopCat

/-!
# Compact symbolic-latent observational quotient

The observational quotient already has a continuous bijection onto the range
of its feature readout.  For compact carriers, this owner supplies the missing
quotient-map witness using Mathlib's compact-to-Hausdorff theorem and packages
the resulting canonical `TopCat` isomorphism.  No new quotient carrier or
analytic latent-space structure is introduced.
-/

namespace InfoGeometry.Topology

open CategoryTheory

theorem symbolicObservationQuotientRangeMap_isQuotientMap
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S) := by
  exact IsQuotientMap.of_surjective_continuous
    (symbolicObservationQuotientRangeEquiv S).surjective
    (continuous_symbolicObservationQuotientRangeMap S)

noncomputable def symbolicObservationQuotientRangeCompactHomeomorph
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    _root_.Quotient (symbolicObservationalSetoid S) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) :=
  symbolicObservationQuotientRangeHomeomorph S
    (symbolicObservationQuotientRangeMap_isQuotientMap S)

noncomputable def symbolicObservationQuotientRangeCompactTopCatHom
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap S)) :=
  symbolicObservationQuotientRangeTopCatHom S

theorem symbolicObservationQuotientRangeCompactTopCatHom_isIso
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    IsIso (symbolicObservationQuotientRangeCompactTopCatHom S) := by
  exact symbolicObservationQuotientRangeTopCatHom_isIso S
    (symbolicObservationQuotientRangeMap_isQuotientMap S)

end InfoGeometry.Topology
