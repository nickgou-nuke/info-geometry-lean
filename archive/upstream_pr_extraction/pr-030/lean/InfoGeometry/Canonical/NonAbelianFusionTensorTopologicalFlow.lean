import InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit

/-!
# Stagewise topological flow on the tensor fusion colimit

This is an algebra-free interface for a continuous one-parameter flow on the
finite tensor carrier.  The colimit construction and its inverse laws are
proved constructively; an analytic Tomita--Takesaki implementation can later
instantiate the interface without changing the topological descent layer.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit
open FilteredColimit.Native.Topological

structure TensorTopologicalFlowData where
  flow : ℝ → (TopCat.of (FusionTensorCarrier ℂ) ⟶
    TopCat.of (FusionTensorCarrier ℂ))
  flow_zero : flow 0 = 𝟙 (TopCat.of (FusionTensorCarrier ℂ))
  flow_add : ∀ t s, flow (t + s) = flow s ≫ flow t

variable (D : TensorTopologicalFlowData)

def flowColimitMap (t : ℝ) :
    topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ)) ⟶
      topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ)) :=
  tensorActionColimitEndomorphism (K := ℂ) (D.flow t)

theorem flowColimitMap_stage (t : ℝ) (n : ℕ) :
    topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        flowColimitMap D t =
      D.flow t ≫ topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n := by
  exact tensorActionColimitEndomorphism_stage (K := ℂ) (D.flow t) n

theorem flowColimitMap_zero :
    flowColimitMap D 0 =
      𝟙 (topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  apply colimit.hom_ext
  intro n
  change topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫ flowColimitMap D 0 =
    topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      𝟙 (topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ)))
  rw [Category.comp_id]
  rw [flowColimitMap_stage]
  rw [D.flow_zero]
  simp

theorem flowColimitMap_add (t s : ℝ) :
    flowColimitMap D (t + s) =
      flowColimitMap D s ≫ flowColimitMap D t := by
  apply colimit.hom_ext
  intro n
  change topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      flowColimitMap D (t + s) =
    topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      (flowColimitMap D s ≫ flowColimitMap D t)
  rw [flowColimitMap_stage]
  calc
    D.flow (t + s) ≫ topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n =
      (D.flow s ≫ D.flow t) ≫ topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n := by rw [D.flow_add]
    _ = D.flow s ≫
        (D.flow t ≫ topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := ℂ)) n) := by
          simp only [Category.assoc]
    _ = D.flow s ≫
        (topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
          flowColimitMap D t) := by
          rw [flowColimitMap_stage]
    _ = (D.flow s ≫ topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := ℂ)) n) ≫
          flowColimitMap D t := by
          simp only [Category.assoc]
    _ = (topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        flowColimitMap D s) ≫ flowColimitMap D t := by
          rw [← flowColimitMap_stage]
    _ = topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        (flowColimitMap D s ≫ flowColimitMap D t) := by
          simp only [Category.assoc]

theorem flowColimitMap_right_inverse (t : ℝ) :
    flowColimitMap D t ≫ flowColimitMap D (-t) =
      𝟙 (topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  rw [← flowColimitMap_add D (-t) t]
  simpa using flowColimitMap_zero D

theorem flowColimitMap_left_inverse (t : ℝ) :
    flowColimitMap D (-t) ≫ flowColimitMap D t =
      𝟙 (topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  rw [← flowColimitMap_add D t (-t)]
  simpa using flowColimitMap_zero D

def flowColimitIso (t : ℝ) :
    topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ)) ≅
      topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ)) where
  hom := flowColimitMap D t
  inv := flowColimitMap D (-t)
  hom_inv_id := flowColimitMap_right_inverse D t
  inv_hom_id := flowColimitMap_left_inverse D t

end InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
