import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Canonical.CuntzGNSFilteredSystem
import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Canonical.FilteredGNSHilbertColimitTopology
import InfoGeometry.Canonical.FilteredGNSTailRepresentationTopology

open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzGNSFilteredSystem
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailRepresentationTopology
open CategoryTheory CategoryTheory.Limits
open FilteredColimit.Native.Topological

noncomputable section

namespace InfoGeometry.Canonical.UHFCuntzGNSColimit

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage (cuntzSystem Stage T))

/-- Continuous star-inductive system underlying the non-commutative Cuntz tower. -/
def cuntzStarSystem : ContinuousStarInductiveSystem Stage :=
  cuntzSystem Stage T

/-- Non-commutative GNS Hilbert space colimit for the Cuntz star algebra tower under a compatible state family. -/
abbrev CuntzKMSHilbertColimit : Type :=
  CuntzGNSHilbertColimit Stage T ω

/-- Stage embedding of the n-th GNS space into the non-commutative Cuntz Hilbert colimit. -/
def cuntzStageToColimit (n : ℕ) :
    CuntzGNSStage Stage T ω n →ₗᵢ[ℂ] CuntzKMSHilbertColimit Stage T ω :=
  cuntzGNSStageToHilbertColimit Stage T ω n

/-- Transition compatibility: Embedding a stage GNS vector through a higher stage matches the direct embedding. -/
@[simp] theorem cuntzStageToColimit_transition
    {m n : ℕ} (hmn : m ≤ n) (x : CuntzGNSStage Stage T ω m) :
    cuntzStageToColimit Stage T ω n (filteredGNSMap Stage (cuntzSystem Stage T) ω hmn x) =
      cuntzStageToColimit Stage T ω m x :=
  cuntzGNSStageToHilbertColimit_transition Stage T ω hmn x

/-- Density theorem: The union of stage GNS images is dense in the Cuntz Hilbert colimit. -/
theorem dense_range_cuntzGNSColimit :
    Dense (⋃ n : ℕ, Set.range (cuntzStageToColimit Stage T ω n)) :=
  dense_iUnion_range_cuntzGNSStageToHilbertColimit Stage T ω

/-- Completeness theorem: The non-commutative Cuntz Hilbert colimit is complete. -/
theorem cuntzGNSColimit_complete :
    CompleteSpace (CuntzKMSHilbertColimit Stage T ω) :=
  cuntzGNSHilbertColimit_complete Stage T ω

/-! ### TopCat realization of the same filtered Cuntz GNS colimit -/

def cuntzStageToColimitContinuousLinearMap (n : ℕ) :
    CuntzGNSStage Stage T ω n →L[ℂ] CuntzKMSHilbertColimit Stage T ω :=
  gnsStageToHilbertColimitContinuousLinearMap
    Stage (cuntzSystem Stage T) ω n

@[simp] theorem cuntzStageToColimitContinuousLinearMap_apply
    (n : ℕ) (x : CuntzGNSStage Stage T ω n) :
    cuntzStageToColimitContinuousLinearMap Stage T ω n x =
      cuntzStageToColimit Stage T ω n x :=
  rfl

@[simp] theorem cuntzStageToColimitContinuousLinearMap_transition
    {m n : ℕ} (hmn : m ≤ n) (x : CuntzGNSStage Stage T ω m) :
    cuntzStageToColimitContinuousLinearMap Stage T ω n
        (filteredGNSMapCLM Stage (cuntzSystem Stage T) ω hmn x) =
      cuntzStageToColimitContinuousLinearMap Stage T ω m x := by
  exact gnsStageToHilbertColimitContinuousLinearMap_transition
    Stage (cuntzSystem Stage T) ω hmn x

def cuntzGNS_topologicalDiagram :
    ℕ ⥤ TopCat :=
  gnsTopologicalDiagram Stage (cuntzSystem Stage T) ω

def cuntzGNS_topologicalCocone :
    Cocone (cuntzGNS_topologicalDiagram Stage T ω) :=
  gnsTopologicalCocone Stage (cuntzSystem Stage T) ω

noncomputable def cuntzGNS_topologicalColimitToHilbert :
    colimit (cuntzGNS_topologicalDiagram Stage T ω) ⟶
      TopCat.of (CuntzKMSHilbertColimit Stage T ω) :=
  gnsTopologicalColimitToHilbert Stage (cuntzSystem Stage T) ω

@[reassoc] theorem cuntzGNS_topologicalColimitToHilbert_stage
    (n : ℕ) :
    colimit.ι (cuntzGNS_topologicalDiagram Stage T ω) n ≫
        cuntzGNS_topologicalColimitToHilbert Stage T ω =
      (cuntzGNS_topologicalCocone Stage T ω).ι.app n := by
  exact gnsTopologicalColimitToHilbert_stage
    Stage (cuntzSystem Stage T) ω n

/-! ### Concrete Cuntz specialization of the tail operator TopCat API -/

def cuntzTailGNSTransitionTopCatHom
    {i₀ : ℕ} {j k : UpperIndex i₀} (hjk : j ≤ k) :
    TopCat.of (CuntzGNSStage Stage T ω j.1) ⟶
      TopCat.of (CuntzGNSStage Stage T ω k.1) :=
  tailGNSTransitionTopCatHom Stage (cuntzSystem Stage T) ω hjk

def cuntzTailGNSOperatorTopCatHom
    {i₀ : ℕ} (a : Stage i₀) (j : UpperIndex i₀) :
    TopCat.of (CuntzGNSStage Stage T ω j.1) ⟶
      TopCat.of (CuntzGNSStage Stage T ω j.1) :=
  tailGNSOperatorTopCatHom Stage (cuntzSystem Stage T) ω a j

theorem cuntzTailGNSOperatorTopCatHom_intertwines
    {i₀ : ℕ} (a : Stage i₀)
    {j k : UpperIndex i₀} (hjk : j ≤ k) :
    cuntzTailGNSTransitionTopCatHom Stage T ω hjk ≫
        cuntzTailGNSOperatorTopCatHom Stage T ω a k =
      cuntzTailGNSOperatorTopCatHom Stage T ω a j ≫
        cuntzTailGNSTransitionTopCatHom Stage T ω hjk := by
  exact tailGNSOperatorTopCatHom_intertwines
    Stage (cuntzSystem Stage T) ω a hjk

end InfoGeometry.Canonical.UHFCuntzGNSColimit
