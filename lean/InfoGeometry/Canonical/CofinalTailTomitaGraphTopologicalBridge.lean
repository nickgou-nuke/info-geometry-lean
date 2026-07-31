import InfoGeometry.Canonical.FilteredGNSTomitaGraphTopologicalColimit
import InfoGeometry.Canonical.FilteredGNSCofinalTailTopological

/-!
# Cofinal-tail transport of closed Tomita graphs

The closed Tomita graph is a relation, not an assumed operator.  Restricting
its stage diagram to an upper (cofinal) tail therefore gives a second
topological colimit.  This owner records its canonical map into the full graph
colimit and its compatible readout into the global Hilbert-pair space.
-/

noncomputable section

namespace CStarStateColimit.Native.CofinalTailTomitaGraphTopologicalBridge

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSCofinalTailTopological
open CStarStateColimit.Native.FilteredGNSTomitaGraphTopologicalColimit
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

abbrev upperGraphTopologicalDiagram (i₀ : I) :
    UpperIndex i₀ ⥤ TopCat :=
  upperIndexInclusion i₀ ⋙ graphTopologicalDiagram Stage sys ω

abbrev upperGraphTopologicalColimit (i₀ : I) : TopCat :=
  topologicalDirectColimit (upperGraphTopologicalDiagram Stage sys ω i₀)

def upperGraphToGraphColimitCocone (i₀ : I) :
    Cocone (upperGraphTopologicalDiagram Stage sys ω i₀) :=
  Cocone.whisker (upperIndexInclusion i₀)
    (colimit.cocone (graphTopologicalDiagram Stage sys ω))

noncomputable def upperGraphTopologicalColimitToGraph (i₀ : I) :
    upperGraphTopologicalColimit Stage sys ω i₀ ⟶
      graphTopologicalColimit Stage sys ω :=
  topologicalDirectDescend
    (upperGraphTopologicalDiagram Stage sys ω i₀)
    (upperGraphToGraphColimitCocone Stage sys ω i₀)

@[reassoc]
theorem upperGraphTopologicalColimitToGraph_stage
    (i₀ : I) (j : UpperIndex i₀) :
    topologicalDirectInjection
        (upperGraphTopologicalDiagram Stage sys ω i₀) j ≫
      upperGraphTopologicalColimitToGraph Stage sys ω i₀ =
      (upperGraphToGraphColimitCocone Stage sys ω i₀).ι.app j := by
  exact topologicalDirectDescend_stage
    (upperGraphTopologicalDiagram Stage sys ω i₀)
    (upperGraphToGraphColimitCocone Stage sys ω i₀) j

def upperGraphToGlobalPairCocone (i₀ : I) :
    Cocone (upperGraphTopologicalDiagram Stage sys ω i₀) :=
  Cocone.whisker (upperIndexInclusion i₀)
    (graphToGlobalPairCocone Stage sys ω)

noncomputable def upperGraphTopologicalColimitToGlobalPair (i₀ : I) :
    upperGraphTopologicalColimit Stage sys ω i₀ ⟶
      TopCat.of (globalGraphPair Stage sys ω) :=
  topologicalDirectDescend
    (upperGraphTopologicalDiagram Stage sys ω i₀)
    (upperGraphToGlobalPairCocone Stage sys ω i₀)

@[simp]
theorem upperGraphTopologicalColimitToGlobalPair_stage
    (i₀ : I) (j : UpperIndex i₀)
    (p : graphCarrier Stage sys ω j.1) :
    upperGraphTopologicalColimitToGlobalPair Stage sys ω i₀
        (topologicalDirectInjection
          (upperGraphTopologicalDiagram Stage sys ω i₀) j p) =
      graphStageToGlobalPair Stage sys ω j.1 p := by
  have h := topologicalDirectDescend_stage
    (upperGraphTopologicalDiagram Stage sys ω i₀)
    (upperGraphToGlobalPairCocone Stage sys ω i₀) j
  exact congrArg (fun f => f p) h

theorem upperGraphTopologicalColimitToGlobalPair_factorization
    (i₀ : I) :
    upperGraphTopologicalColimitToGlobalPair Stage sys ω i₀ =
      upperGraphTopologicalColimitToGraph Stage sys ω i₀ ≫
        graphTopologicalColimitToGlobalPair Stage sys ω := by
  symm
  apply topologicalDirectDescend_unique
    (upperGraphTopologicalDiagram Stage sys ω i₀)
    (upperGraphToGlobalPairCocone Stage sys ω i₀)
  intro j
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [← Category.assoc, upperGraphTopologicalColimitToGraph_stage]
  change
    graphTopologicalColimitToGlobalPair Stage sys ω
        ((colimit.cocone (graphTopologicalDiagram Stage sys ω)).ι.app j.1 p) =
      graphStageToGlobalPair Stage sys ω j.1 p
  exact graphTopologicalColimitToGlobalPair_stage Stage sys ω j.1 p

theorem upperGraphTopologicalColimitToGlobalPair_mem_globalTomitaGraphClosure
    (i₀ : I) (x : upperGraphTopologicalColimit Stage sys ω i₀) :
    upperGraphTopologicalColimitToGlobalPair Stage sys ω i₀ x ∈
      globalTomitaGraphClosure Stage sys ω := by
  apply subset_closure
  refine ⟨upperGraphTopologicalColimitToGraph Stage sys ω i₀ x, ?_⟩
  have h := congrArg (fun f => f x)
    (upperGraphTopologicalColimitToGlobalPair_factorization
      Stage sys ω i₀)
  simpa only [TopCat.comp_app] using h.symm

theorem upperGraphTopologicalColimitToGlobalPair_fst_mem_globalTomitaDomain
    (i₀ : I) (x : upperGraphTopologicalColimit Stage sys ω i₀) :
    (upperGraphTopologicalColimitToGlobalPair Stage sys ω i₀ x).1 ∈
      globalTomitaDomain Stage sys ω := by
  refine ⟨(upperGraphTopologicalColimitToGlobalPair Stage sys ω i₀ x).2, ?_⟩
  exact upperGraphTopologicalColimitToGlobalPair_mem_globalTomitaGraphClosure
    Stage sys ω i₀ x

end CStarStateColimit.Native.CofinalTailTomitaGraphTopologicalBridge
