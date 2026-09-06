import InfoGeometry.Canonical.RealUHFCompatibleReadoutStageAction

/-!
# Colimit action induced by the compatible finite-stage scalar flows

The finite-stage flows form a TopCat cocone after postcomposition with the
canonical colimit injections.  The colimit universal property then produces
the global topological endomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

def stageFlowTopCatHom (n : ℕ) (t : ℝ) :
    TopCat.of (Stage n) ⟶ TopCat.of (Stage n) :=
  TopCat.ofHom
    (ContinuousMap.mk (scalarDilationStageFlow.flow n t)
      (scalarDilationStageFlow.flow n t).continuous)

theorem stageFlow_bond_naturality
    (t : ℝ) {m n : ℕ} (f : m ⟶ n)
    (A : Stage m) :
    (bondCLM m n (leOfHom f))
        ((scalarDilationStageFlow.flow m t) A) =
      (scalarDilationStageFlow.flow n t)
        ((bondCLM m n (leOfHom f)) A) := by
  rw [scalarDilationStageFlow_apply, scalarDilationStageFlow_apply]
  rw [map_smul]

def scalarDilationTopologicalCocone (t : ℝ) :
    Cocone topologicalDiagram where
  pt := topologicalColimit
  ι :=
    { app := fun n => stageFlowTopCatHom n t ≫ topologicalInjection n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        change (topologicalInjection n)
              ((scalarDilationStageFlow.flow n t)
                ((bondAlgHom m n (leOfHom f)) A)) =
          (topologicalInjection m)
            ((scalarDilationStageFlow.flow m t) A)
        rw [← topologicalInjection_transition (leOfHom f)
          ((scalarDilationStageFlow.flow m t) A)]
        congr 1
        simpa only [bondCLM_apply] using
          (stageFlow_bond_naturality t f A).symm
    }

noncomputable def scalarDilationTopologicalColimitAction (t : ℝ) :
    topologicalColimit ⟶ topologicalColimit :=
  colimit.desc topologicalDiagram
    (scalarDilationTopologicalCocone t)

theorem scalarDilationTopologicalColimitAction_inclusion
    (t : ℝ) (n : ℕ) (A : Stage n) :
    scalarDilationTopologicalColimitAction t
        (topologicalInjection n A) =
      topologicalInjection n
        ((scalarDilationStageFlow.flow n t) A) := by
  change (colimit.desc topologicalDiagram
      (scalarDilationTopologicalCocone t))
        (topologicalInjection n A) =
    ((scalarDilationTopologicalCocone t).ι.app n) A
  have h := topologicalDirectDescend_stage
    topologicalDiagram (scalarDilationTopologicalCocone t) n
  exact congrArg (fun f => f A) h

theorem scalarDilationTopologicalColimitAction_zero :
    scalarDilationTopologicalColimitAction 0 =
      𝟙 topologicalColimit := by
  symm
  apply topologicalDirectDescend_unique topologicalDiagram
    (scalarDilationTopologicalCocone 0) (𝟙 topologicalColimit)
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change (topologicalInjection n) A =
    (topologicalInjection n)
      ((scalarDilationStageFlow.flow n 0) A)
  rw [scalarDilationStageFlow.flow_zero]
  rfl

theorem scalarDilationTopologicalColimitAction_add
    (s t : ℝ) :
    scalarDilationTopologicalColimitAction (s + t) =
      scalarDilationTopologicalColimitAction t ≫
        scalarDilationTopologicalColimitAction s := by
  symm
  apply topologicalDirectDescend_unique topologicalDiagram
    (scalarDilationTopologicalCocone (s + t))
    (scalarDilationTopologicalColimitAction t ≫
      scalarDilationTopologicalColimitAction s)
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change scalarDilationTopologicalColimitAction s
      (scalarDilationTopologicalColimitAction t
        (topologicalInjection n A)) =
    topologicalInjection n
      ((scalarDilationStageFlow.flow n (s + t)) A)
  rw [scalarDilationTopologicalColimitAction_inclusion,
    scalarDilationTopologicalColimitAction_inclusion]
  have h := congrArg (fun f => f A)
    (scalarDilationStageFlow.flow_add n s t)
  exact congrArg (fun X => topologicalInjection n X) h.symm

end InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction
