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
  flow : ℝ → (TopCat.of (FusionTensorCarrier ℂ) ≅
    TopCat.of (FusionTensorCarrier ℂ))
  flow_add : ∀ t s, (flow (t + s)).hom =
    (flow s).hom ≫ (flow t).hom

variable (D : TensorTopologicalFlowData)

theorem flow_zero : D.flow 0 =
    Iso.refl (TopCat.of (FusionTensorCarrier ℂ)) := by
  apply Iso.ext
  apply (cancel_mono (D.flow 1).hom).1
  simpa using (D.flow_add 1 0).symm

def flowColimitMap (t : ℝ) :
    colimit
        (fusionTensorTopologicalDiagram (K := ℂ)) ⟶
      colimit
        (fusionTensorTopologicalDiagram (K := ℂ)) :=
  tensorActionColimitEndomorphism (K := ℂ) (D.flow t).hom

theorem flowColimitMap_stage (t : ℝ) (n : ℕ) :
    colimit.ι
        (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        flowColimitMap D t =
      (D.flow t).hom ≫ colimit.ι
        (fusionTensorTopologicalDiagram (K := ℂ)) n := by
  exact tensorActionColimitEndomorphism_stage (K := ℂ) (D.flow t).hom n

theorem flowColimitMap_zero :
    flowColimitMap D 0 =
      𝟙 (colimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  apply colimit.hom_ext
  intro n
  change colimit.ι
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫ flowColimitMap D 0 =
    colimit.ι
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      𝟙 (colimit
        (fusionTensorTopologicalDiagram (K := ℂ)))
  rw [Category.comp_id]
  rw [flowColimitMap_stage]
  rw [flow_zero D]
  simp

theorem flowColimitMap_add (t s : ℝ) :
    flowColimitMap D (t + s) =
      flowColimitMap D s ≫ flowColimitMap D t := by
  apply colimit.hom_ext
  intro n
  change colimit.ι
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      flowColimitMap D (t + s) =
    colimit.ι
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      (flowColimitMap D s ≫ flowColimitMap D t)
  rw [flowColimitMap_stage]
  calc
    (D.flow (t + s)).hom ≫ colimit.ι
        (fusionTensorTopologicalDiagram (K := ℂ)) n =
      ((D.flow s).hom ≫ (D.flow t).hom) ≫ colimit.ι
        (fusionTensorTopologicalDiagram (K := ℂ)) n := by rw [D.flow_add]
    _ = (D.flow s).hom ≫
        ((D.flow t).hom ≫ colimit.ι
          (fusionTensorTopologicalDiagram (K := ℂ)) n) := by
          simp only [Category.assoc]
    _ = (D.flow s).hom ≫
        (colimit.ι
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
          flowColimitMap D t) := by
          rw [flowColimitMap_stage]
    _ = ((D.flow s).hom ≫ colimit.ι
          (fusionTensorTopologicalDiagram (K := ℂ)) n) ≫
          flowColimitMap D t := by
          simp only [Category.assoc]
    _ = (colimit.ι
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        flowColimitMap D s) ≫ flowColimitMap D t := by
          rw [← flowColimitMap_stage]
    _ = colimit.ι
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        (flowColimitMap D s ≫ flowColimitMap D t) := by
          simp only [Category.assoc]

theorem flowColimitMap_right_inverse (t : ℝ) :
    flowColimitMap D t ≫ flowColimitMap D (-t) =
      𝟙 (colimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  rw [← flowColimitMap_add D (-t) t]
  simpa using flowColimitMap_zero D

theorem flowColimitMap_left_inverse (t : ℝ) :
    flowColimitMap D (-t) ≫ flowColimitMap D t =
      𝟙 (colimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  rw [← flowColimitMap_add D t (-t)]
  simpa using flowColimitMap_zero D

def flowColimitIso (t : ℝ) :
    colimit
        (fusionTensorTopologicalDiagram (K := ℂ)) ≅
      colimit
        (fusionTensorTopologicalDiagram (K := ℂ)) where
  hom := flowColimitMap D t
  inv := flowColimitMap D (-t)
  hom_inv_id := flowColimitMap_right_inverse D t
  inv_hom_id := flowColimitMap_left_inverse D t

end InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
