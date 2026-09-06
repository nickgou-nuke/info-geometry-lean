import InfoGeometry.Topology.SymbolicLatentAtlasCechCocycleTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of atlas overlaps

Atlas domains are open and are not compact by default.  This owner therefore
requires an explicit compactness property for an overlap and packages only
the overlap carrier in `CompHaus`.  The feature transition maps remain
`TopCat` morphisms, because the feature space is not assumed compact.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentAtlasOverlapCompHaus
    {X ι κ : Type} [TopologicalSpace X]
    [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ)
    (hcompact : IsCompact (A.overlap i j))
    [T2Space (SymbolicLatentAtlasOverlap A i j)] : CompHaus := by
  letI : CompactSpace (SymbolicLatentAtlasOverlap A i j) :=
    isCompact_iff_compactSpace.mp hcompact
  exact CompHaus.of (SymbolicLatentAtlasOverlap A i j)

def SymbolicLatentAtlas.overlapObservationCompHausTopCatHom
    {X ι κ : Type} [TopologicalSpace X]
    [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ)
    (hcompact : IsCompact (A.overlap i j))
    [T2Space (SymbolicLatentAtlasOverlap A i j)] (k : κ) :
    compHausToTop.obj (symbolicLatentAtlasOverlapCompHaus A i j hcompact) ⟶
      TopCat.of (ι → ℝ) := by
  change TopCat.of (SymbolicLatentAtlasOverlap A i j) ⟶ TopCat.of (ι → ℝ)
  exact A.overlapObservationTopCatHom k i j

@[simp] theorem SymbolicLatentAtlas.overlapObservationCompHausTopCatHom_apply
    {X ι κ : Type} [TopologicalSpace X]
    [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ)
    (hcompact : IsCompact (A.overlap i j))
    [T2Space (SymbolicLatentAtlasOverlap A i j)] (k : κ)
    (x : SymbolicLatentAtlasOverlap A i j) :
    A.overlapObservationCompHausTopCatHom i j hcompact k x =
      symbolicObservationMap (A.chart k).system x.1 :=
  rfl

theorem SymbolicLatentAtlas.overlapObservationCompHaus_cech_cocycle
    {X ι κ : Type} [TopologicalSpace X]
    [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j k : κ}
    (hcompact : IsCompact (A.overlap i k))
    [T2Space (SymbolicLatentAtlasOverlap A i k)]
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (Hik : SymbolicLatentAtlasCompatibility A i k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    A.overlapObservationCompHausTopCatHom i k hcompact i ≫
        Hik.featureTransitionTopCatHom =
      A.overlapObservationCompHausTopCatHom i k hcompact i ≫
        Hij.featureTransitionTopCatHom ≫ Hjk.featureTransitionTopCatHom := by
  exact A.overlapObservation_transition_cech_cocycle Hij Hjk Hik hmiddle

theorem SymbolicLatentAtlas.overlapObservationCompHaus_transition_commutes
    {X ι κ : Type} [TopologicalSpace X]
    [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ}
    (hcompact : IsCompact (A.overlap i j))
    [T2Space (SymbolicLatentAtlasOverlap A i j)]
    (H : SymbolicLatentAtlasCompatibility A i j) :
    A.overlapObservationCompHausTopCatHom i j hcompact i ≫
        H.featureTransitionTopCatHom =
      A.overlapObservationCompHausTopCatHom i j hcompact j := by
  exact A.overlapObservation_transition_commutes H

end InfoGeometry.Topology
