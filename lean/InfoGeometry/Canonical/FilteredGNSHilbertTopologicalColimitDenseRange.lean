import InfoGeometry.Canonical.FilteredGNSHilbertColimitTopology

/-!
# Dense range of the canonical GNS topological-colimit map

The generic filtered-GNS owner supplies a dense union of finite-stage images.
The topological cocone map sends each categorical stage injection to exactly
that image.  Hence its range is dense, by a direct `Dense.mono` argument.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSHilbertColimitTopology

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

theorem denseRange_gnsTopologicalColimitToHilbert :
    DenseRange (gnsTopologicalColimitToHilbert Stage sys ω) := by
  have hsub :
      (⋃ i : I,
        Set.range
          (gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i)) ⊆
        Set.range (gnsTopologicalColimitToHilbert Stage sys ω) := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, ⟨x, rfl⟩⟩
    refine ⟨topologicalDirectInjection
      (gnsTopologicalDiagram Stage sys ω) i x, ?_⟩
    have h := congrArg (fun f => f x)
      (gnsTopologicalColimitToHilbert_stage Stage sys ω i)
    simpa [TopCat.comp_app] using h
  exact Dense.mono hsub
    (dense_iUnion_range_gnsStageToHilbertColimitContinuousLinearMap
      Stage sys ω)

end CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
