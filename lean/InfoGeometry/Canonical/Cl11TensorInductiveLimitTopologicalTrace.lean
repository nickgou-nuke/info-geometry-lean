import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalComparison
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge

/-!
# Normalized-trace readout for the Clifford `TopCat` colimit

The algebraic-to-topological comparison lands in the native `TopCat` colimit
of the Clifford matrix tower.  This owner supplies the compatible normalized
trace cocone for that exact diagram and records its finite-stage readback.
It still does not identify the colimit with a completed UHF/CAR algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open FilteredColimit.Native.Topological

theorem normalizedTrace_bondAlgHom
    (m n : ℕ) (h : m ≤ n) (A : MatStage m) :
    normalizedTrace n (bondAlgHom m n h A) = normalizedTrace m A := by
  induction h with
  | refl =>
      simp [bondAlgHom_refl]
  | @step n h ih =>
      rw [bondAlgHom_succ m n h]
      change normalizedTrace (n + 1)
        (stageEmbed n (bondAlgHom m n h A)) = normalizedTrace m A
      rw [stageEmbed_apply, normalizedTrace_matStageEmbed, ih]

def normalizedTraceTopologicalCocone : Cocone topologicalDiagram where
  pt := TopCat.of ℝ
  ι :=
    { app := fun n => normalizedTraceTopCatHom n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        change normalizedTrace n
            (bondAlgHom m n (leOfHom f) A) = normalizedTrace m A
        exact normalizedTrace_bondAlgHom m n (leOfHom f) A }

noncomputable def normalizedTraceTopologicalColimitMap :
    topologicalColimit ⟶ TopCat.of ℝ :=
  colimit.desc topologicalDiagram normalizedTraceTopologicalCocone

theorem normalizedTraceTopologicalColimitMap_inclusion
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (topologicalInjection n A) = normalizedTrace n A := by
  have h := topologicalDirectDescend_stage
    topologicalDiagram normalizedTraceTopologicalCocone n
  exact congrArg (fun f => f A) h

theorem normalizedTraceTopologicalColimitMap_algebraic_stage
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (algebraicToTopological (ofStage n A)) = normalizedTrace n A := by
  rw [algebraicToTopological_ofStage]
  exact normalizedTraceTopologicalColimitMap_inclusion n A

theorem normalizedTraceTopologicalColimitMap_unique
    (f : topologicalColimit ⟶ TopCat.of ℝ)
    (hf : ∀ (n : ℕ) (A : MatStage n),
      f (topologicalInjection n A) = normalizedTrace n A) :
    f = normalizedTraceTopologicalColimitMap := by
  apply topologicalDirectDescend_unique topologicalDiagram
    normalizedTraceTopologicalCocone f
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change f (topologicalInjection n A) = normalizedTrace n A
  exact hf n A

