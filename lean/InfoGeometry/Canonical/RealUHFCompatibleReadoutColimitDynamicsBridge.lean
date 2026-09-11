import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace

/-!
# Normalized-trace covariance at the topological colimit boundary

The scalar stage flow is represented on the colimit readout by postcomposition
with a continuous scalar map on `ℝ`.  This is a readout covariance theorem on
stage representatives, not a claim that the colimit itself carries a global
algebra automorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge

open CategoryTheory
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Clifford.Cl11TensorTower

def scalarValueMap (t : ℝ) : TopCat.of ℝ ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun x => (Real.exp t) * x
      continuous_toFun :=
        continuous_const.mul continuous_id }

@[simp] theorem scalarValueMap_apply (t x : ℝ) :
    scalarValueMap t x = (Real.exp t) * x := rfl

theorem scalarValueMap_zero :
    scalarValueMap 0 = 𝟙 (TopCat.of ℝ) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (Real.exp 0) * x = x
  simp

theorem scalarValueMap_add (s t : ℝ) :
    scalarValueMap (s + t) =
      scalarValueMap s ≫ scalarValueMap t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (Real.exp (s + t)) * x =
    (Real.exp t) * ((Real.exp s) * x)
  rw [Real.exp_add]
  ring

theorem normalizedTrace_scalarValueMap_stage
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    (normalizedTraceTopologicalColimitMap ≫ scalarValueMap t)
        (topologicalInjection n X) =
      (Real.exp t) •
        normalizedTraceTopologicalColimitMap (topologicalInjection n X) := by
  change (Real.exp t) *
      normalizedTraceTopologicalColimitMap (topologicalInjection n X) = _
  rw [smul_eq_mul]

theorem normalizedTrace_scalarValueMap_matches_stageFlow
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    (normalizedTraceTopologicalColimitMap ≫ scalarValueMap t)
        (topologicalInjection n X) =
      normalizedTraceTopologicalColimitMap
        (topologicalInjection n (scalarDilationStageFlow.flow n t X)) := by
  rw [normalizedTrace_scalarValueMap_stage]
  exact (normalizedTraceColimitMap_scalarDilation_stage t n X).symm

theorem normalizedTrace_colimit_readout_zero :
    normalizedTraceTopologicalColimitMap ≫ scalarValueMap 0 =
      normalizedTraceTopologicalColimitMap := by
  rw [scalarValueMap_zero, Category.comp_id]

theorem normalizedTrace_colimit_readout_add
    (s t : ℝ) :
    normalizedTraceTopologicalColimitMap ≫ scalarValueMap (s + t) =
      (normalizedTraceTopologicalColimitMap ≫ scalarValueMap s) ≫
        scalarValueMap t := by
  rw [scalarValueMap_add]
  simp only [Category.assoc]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge
