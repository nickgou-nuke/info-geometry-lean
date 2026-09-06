import Mathlib
import InfoGeometry.Topology.SymbolicLatentAtlasOverlapTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Čech cocycle law for symbolic-latent atlas transitions

On the triple-overlap carrier, a direct transition from chart `i` to chart
`k` agrees with the composite of the transitions `i → j → k`.  The proof is
pointwise through the common observation map; no gluing ax!om or abstract
descent property is introduced.
-/

theorem SymbolicLatentAtlas.overlapObservation_transition_cech_cocycle
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (Hik : SymbolicLatentAtlasCompatibility A i k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    A.overlapObservationTopCatHom i i k ≫ Hik.featureTransitionTopCatHom =
      A.overlapObservationTopCatHom i i k ≫
        Hij.featureTransitionTopCatHom ≫ Hjk.featureTransitionTopCatHom := by
  calc
    A.overlapObservationTopCatHom i i k ≫ Hik.featureTransitionTopCatHom =
        A.overlapObservationTopCatHom k i k :=
      A.overlapObservation_transition_commutes Hik
    _ = A.overlapObservationTopCatHom i i k ≫
        Hij.featureTransitionTopCatHom ≫ Hjk.featureTransitionTopCatHom :=
      (A.overlapObservation_transition_comp_commutes Hij Hjk hmiddle).symm

end InfoGeometry.Topology
