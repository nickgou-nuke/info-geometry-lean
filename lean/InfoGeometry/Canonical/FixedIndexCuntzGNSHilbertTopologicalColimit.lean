import InfoGeometry.Canonical.FixedIndexCuntzStarTower
import InfoGeometry.Canonical.FilteredGNSHilbertColimitTopology
import InfoGeometry.Canonical.FilteredGNSHilbertTopologicalColimitDenseRange

/-!
# Topological API for the fixed-index Cuntz GNS colimit

The generic filtered-GNS owner already constructs the continuous stage
diagram and its cocone.  This file exposes those categorical maps through the
fixed-index Cuntz tower interface, without introducing another completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzGNSHilbertTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
open FilteredColimit.Native.Topological

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {ωStage : ℕ → Type}
variable [∀ n, CStarAlgebra (ωStage n)]
variable [∀ n, PartialOrder (ωStage n)]
variable [∀ n, StarOrderedRing (ωStage n)]
variable (T : Data (ι := ι) ωStage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
    ωStage (fixedIndexSystem (ι := ι) T))

abbrev stageDiagram : ℕ ⥤ TopCat :=
  gnsTopologicalDiagram ωStage (fixedIndexSystem (ι := ι) T) ω

abbrev stageCocone : Cocone (stageDiagram (ι := ι) T ω) :=
  gnsTopologicalCocone ωStage (fixedIndexSystem (ι := ι) T) ω

abbrev topologicalColimit : TopCat :=
  colimit (stageDiagram (ι := ι) T ω)

def stageInjection (n : ℕ) :
    (stageDiagram (ι := ι) T ω).obj n ⟶ topologicalColimit (ι := ι) T ω :=
  colimit.ι (stageDiagram (ι := ι) T ω) n

noncomputable def colimitToHilbert :
    topologicalColimit (ι := ι) T ω ⟶
      TopCat.of (fixedIndexGNSHilbertColimit (ι := ι) T ω) :=
  gnsTopologicalColimitToHilbert
    ωStage (fixedIndexSystem (ι := ι) T) ω

@[reassoc] theorem colimitToHilbert_stage (n : ℕ) :
    stageInjection (ι := ι) T ω n ≫
        colimitToHilbert (ι := ι) T ω =
      (stageCocone (ι := ι) T ω).ι.app n :=
  gnsTopologicalColimitToHilbert_stage
    ωStage (fixedIndexSystem (ι := ι) T) ω n

theorem dense_stage_images :
    Dense
      (⋃ n : ℕ,
        Set.range
          (gnsStageToHilbertColimitContinuousLinearMap
            ωStage (fixedIndexSystem (ι := ι) T) ω n)) :=
  dense_iUnion_range_gnsStageToHilbertColimitContinuousLinearMap
    ωStage (fixedIndexSystem (ι := ι) T) ω

theorem denseRange_colimitToHilbert :
    DenseRange (colimitToHilbert (ι := ι) T ω) :=
  denseRange_gnsTopologicalColimitToHilbert
    ωStage (fixedIndexSystem (ι := ι) T) ω

end InfoGeometry.Canonical.FixedIndexCuntzGNSHilbertTopologicalColimit
