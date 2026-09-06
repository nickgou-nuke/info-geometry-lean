import InfoGeometry.Topology.SymbolicLatentFeasibleObservationCompHausNaturality
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHausFlow

/-!
# Flow invariance of the feasible symbolic-latent observation

The symbolic flow preserves every observable coordinate.  Consequently its
`CompHaus` time-slice acts trivially after passing to the feasible observation
region.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [Fintype ι]

theorem SymbolicLatentFlow.feasibleObservationCompHausFlow_invariant
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i))
    (t : ℝ) :
    (symbolicLatentFeasibleSubspaceCompHausFlowIso
      F targets hclosed t).hom ≫
        symbolicLatentFeasibleRegionObservationCompHausHom
          S targets hclosed hcompact =
      symbolicLatentFeasibleRegionObservationCompHausHom
        S targets hclosed hcompact := by
  dsimp [symbolicLatentFeasibleSubspaceCompHaus,
    symbolicLatentFeasibleFeatureRegionCompHaus]
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change symbolicObservationMap S (F.act t (x : X)) =
    symbolicObservationMap S (x : X)
  exact F.preserves_observation t (x : X)

@[simp] theorem SymbolicLatentFlow.feasibleObservationCompHausFlow_invariant_apply
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i))
    (t : ℝ)
    (x : feasibleLatentSubspace S targets) :
    ((symbolicLatentFeasibleSubspaceCompHausFlowIso
      F targets hclosed t).hom ≫
        symbolicLatentFeasibleRegionObservationCompHausHom
          S targets hclosed hcompact) x =
      symbolicLatentFeasibleRegionObservationCompHausHom
        S targets hclosed hcompact x :=
  congrArg (fun h => h x)
    (F.feasibleObservationCompHausFlow_invariant
      targets hclosed hcompact t)

end InfoGeometry.Topology

