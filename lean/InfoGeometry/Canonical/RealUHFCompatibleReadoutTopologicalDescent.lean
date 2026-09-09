import InfoGeometry.Canonical.RealUHFCompatibleReadoutContinuousColimitAction

/-!
# Descent of the scalar readout through the topological colimit

For each time parameter a scaled normalized-trace cocone is descended through
the native `TopCat` colimit.  The descended map is then identified with scalar
postcomposition of the existing normalized-trace colimit map.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalDescent

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

def normalizedTraceScaledTopologicalCocone (t : ℝ) :
    Cocone topologicalDiagram where
  pt := TopCat.of ℝ
  ι :=
    { app := fun n => normalizedTraceTopCatHom n ≫ scalarValueMap t
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        change (Real.exp t) *
            normalizedTrace n (bondAlgHom m n (leOfHom f) A) =
          (Real.exp t) * normalizedTrace m A
        rw [normalizedTrace_bondAlgHom] }

noncomputable def normalizedTraceReadoutAtTime (t : ℝ) :
    topologicalColimit ⟶ TopCat.of ℝ :=
  colimit.desc topologicalDiagram
    (normalizedTraceScaledTopologicalCocone t)

theorem normalizedTraceReadoutAtTime_inclusion
    (t : ℝ) (n : ℕ) (A : MatStage n) :
    normalizedTraceReadoutAtTime t
        (topologicalInjection n A) =
      (Real.exp t) * normalizedTrace n A := by
  change (colimit.desc topologicalDiagram
      (normalizedTraceScaledTopologicalCocone t))
        (topologicalInjection n A) =
    ((normalizedTraceScaledTopologicalCocone t).ι.app n) A
  have h := topologicalDirectDescend_stage
    topologicalDiagram (normalizedTraceScaledTopologicalCocone t) n
  exact congrArg (fun f => f A) h

theorem normalizedTraceReadoutAtTime_eq_postcomposition
    (t : ℝ) :
    normalizedTraceReadoutAtTime t =
      normalizedTraceTopologicalColimitMap ≫ scalarValueMap t := by
  symm
  apply topologicalDirectDescend_unique topologicalDiagram
    (normalizedTraceScaledTopologicalCocone t)
    (normalizedTraceTopologicalColimitMap ≫ scalarValueMap t)
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change scalarValueMap t
      (normalizedTraceTopologicalColimitMap
        (topologicalInjection n A)) =
    scalarValueMap t (normalizedTraceTopCatHom n A)
  rw [normalizedTraceTopologicalColimitMap_inclusion]
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalDescent
end
