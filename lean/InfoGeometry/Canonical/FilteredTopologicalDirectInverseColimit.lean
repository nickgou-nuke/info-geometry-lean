import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Native topological direct and inverse colimit interfaces

This owner exposes the categorical universal properties in `TopCat` directly.
The constructions are the Mathlib `colimit` and `limit`; no replacement by a
sequence, coordinate chart, metric epsilon argument, or finite enumeration is
made.  The stage laws below are the exact continuous-map equations supplied
by the universal properties.
-/

noncomputable section

namespace FilteredColimit.Native.Topological

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J]

/-- The categorical topological direct colimit of a diagram. -/
noncomputable def topologicalDirectColimit
    (F : J ⥤ TopCat.{u}) : TopCat.{u} :=
  colimit F

/-- Canonical continuous stage map into a topological direct colimit. -/
noncomputable def topologicalDirectInjection
    (F : J ⥤ TopCat.{u}) (j : J) :
    F.obj j ⟶ topologicalDirectColimit F :=
  colimit.ι F j

/-- Descend a continuous cocone through the topological direct colimit. -/
noncomputable def topologicalDirectDescend
    (F : J ⥤ TopCat.{u}) (c : Cocone F) :
    topologicalDirectColimit F ⟶ c.pt :=
  colimit.desc F c

@[reassoc]
theorem topologicalDirectDescend_stage
    (F : J ⥤ TopCat.{u}) (c : Cocone F) (j : J) :
    topologicalDirectInjection F j ≫ topologicalDirectDescend F c =
      c.ι.app j := by
  exact colimit.ι_desc c j

theorem topologicalDirectDescend_unique
    (F : J ⥤ TopCat.{u}) (c : Cocone F)
    (f : topologicalDirectColimit F ⟶ c.pt)
    (h : ∀ j : J,
      topologicalDirectInjection F j ≫ f = c.ι.app j) :
    f = topologicalDirectDescend F c := by
  apply colimit.hom_ext
  intro j
  change topologicalDirectInjection F j ≫ f =
    topologicalDirectInjection F j ≫ topologicalDirectDescend F c
  rw [h j, topologicalDirectDescend_stage]

/-- The categorical topological inverse limit of a diagram. -/
noncomputable def topologicalInverseLimit
    (F : J ⥤ TopCat.{u}) : TopCat.{u} :=
  limit F

/-- Canonical continuous projection from a topological inverse limit. -/
noncomputable def topologicalInverseProjection
    (F : J ⥤ TopCat.{u}) (j : J) :
    topologicalInverseLimit F ⟶ F.obj j :=
  limit.π F j

/-- Lift a compatible continuous cone into a topological inverse limit. -/
noncomputable def topologicalInverseLift
    (F : J ⥤ TopCat.{u}) (c : Cone F) :
    c.pt ⟶ topologicalInverseLimit F :=
  limit.lift F c

@[reassoc]
theorem topologicalInverseLift_projection
    (F : J ⥤ TopCat.{u}) (c : Cone F) (j : J) :
    topologicalInverseLift F c ≫ topologicalInverseProjection F j =
      c.π.app j := by
  exact limit.lift_π c j

theorem topologicalInverseLift_unique
    (F : J ⥤ TopCat.{u}) (c : Cone F)
    (f : c.pt ⟶ topologicalInverseLimit F)
    (h : ∀ j : J,
      f ≫ topologicalInverseProjection F j = c.π.app j) :
    f = topologicalInverseLift F c := by
  apply limit.hom_ext
  intro j
  change f ≫ topologicalInverseProjection F j =
    topologicalInverseLift F c ≫ topologicalInverseProjection F j
  rw [h j, topologicalInverseLift_projection]

end FilteredColimit.Native.Topological
