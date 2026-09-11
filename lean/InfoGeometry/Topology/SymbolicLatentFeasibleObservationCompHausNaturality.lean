import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHausFunctor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentFeasibleRegionObservationCompHaus

/-!
# Naturality of feasible symbolic-latent observation

The observation of a feasible latent point is unchanged by a symbolic-latent
morphism, because morphisms intertwine every observable coordinate.  This
owner records that fact as a genuine natural transformation in `CompHaus`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [Fintype ι]

noncomputable def symbolicLatentFeasibleObservationCompHausNatTrans
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i)) :
    symbolicLatentFeasibleSubspaceCompHausFunctor targets hclosed ⟶
      ((Functor.const (FiniteSymbolicLatentSystem X ι)).obj
        (symbolicLatentFeasibleFeatureRegionCompHaus targets hcompact)) := by
  refine
    { app := fun S =>
        symbolicLatentFeasibleRegionObservationCompHausHom
          S targets hclosed hcompact
      naturality := ?_ }
  intro S T F
  change
    (symbolicLatentFeasibleSubspaceCompHausHom F targets hclosed ≫
        symbolicLatentFeasibleRegionObservationCompHausHom
          T targets hclosed hcompact) =
      symbolicLatentFeasibleRegionObservationCompHausHom
        S targets hclosed hcompact
  dsimp [symbolicLatentFeasibleSubspaceCompHaus,
    symbolicLatentFeasibleFeatureRegionCompHaus]
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change symbolicObservationMap T (F.toFun x) =
    symbolicObservationMap S x
  exact funext (fun i => F.intertwines i x)

theorem symbolicLatentFeasibleObservationCompHausNatTrans_naturality_apply
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i))
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : S ⟶ T)
    (x : feasibleLatentSubspace S targets) :
    ((symbolicLatentFeasibleSubspaceCompHausFunctor targets hclosed).map F ≫
        (symbolicLatentFeasibleObservationCompHausNatTrans
          targets hclosed hcompact).app T) x =
      ((symbolicLatentFeasibleObservationCompHausNatTrans
          targets hclosed hcompact).app S ≫
        ((Functor.const (FiniteSymbolicLatentSystem X ι)).obj
          (symbolicLatentFeasibleFeatureRegionCompHaus targets hcompact)).map F) x :=
  congrArg (fun h => h x)
    ((symbolicLatentFeasibleObservationCompHausNatTrans
      targets hclosed hcompact).naturality F)

end InfoGeometry.Topology
