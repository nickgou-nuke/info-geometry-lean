import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

@[reassoc (attr := simp)]
theorem topologicalDirectInjection_naturality
    (F : J ⥤ TopCat.{u}) {j j' : J} (f : j ⟶ j') :
    F.map f ≫ topologicalDirectInjection F j' =
      topologicalDirectInjection F j := by
  exact colimit.w F f

theorem topologicalDirectInjection_naturality_apply
    (F : J ⥤ TopCat.{u}) {j j' : J} (f : j ⟶ j')
    (x : F.obj j) :
    topologicalDirectInjection F j' (F.map f x) =
      topologicalDirectInjection F j x := by
  exact congrArg (fun g => g x)
    (topologicalDirectInjection_naturality F f)

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

theorem topologicalDirectDescend_stage_apply
    (F : J ⥤ TopCat.{u}) (c : Cocone F) (j : J)
    (x : F.obj j) :
    topologicalDirectDescend F c (topologicalDirectInjection F j x) =
      c.ι.app j x := by
  exact congrArg (fun g => g x) (topologicalDirectDescend_stage F c j)

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

/-- The canonical TopCat isomorphism induced by a natural isomorphism of diagrams. -/
noncomputable def topologicalDirectColimitIso
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    topologicalDirectColimit F ≅ topologicalDirectColimit G :=
  HasColimit.isoOfNatIso w

@[reassoc (attr := simp)]
theorem topologicalDirectColimitIso_hom_stage
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    topologicalDirectInjection F j ≫
        (topologicalDirectColimitIso w).hom =
      w.hom.app j ≫ topologicalDirectInjection G j := by
  exact HasColimit.isoOfNatIso_ι_hom w j

@[reassoc (attr := simp)]
theorem topologicalDirectColimitIso_inv_stage
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    topologicalDirectInjection G j ≫
        (topologicalDirectColimitIso w).inv =
      w.inv.app j ≫ topologicalDirectInjection F j := by
  exact HasColimit.isoOfNatIso_ι_inv w j

theorem topologicalDirectColimitIso_hom_stage_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : F.obj j) :
    (topologicalDirectColimitIso w).hom
        (topologicalDirectInjection F j x) =
      topologicalDirectInjection G j (w.hom.app j x) := by
  exact congrArg (fun f => f x)
    (topologicalDirectColimitIso_hom_stage w j)

theorem topologicalDirectColimitIso_inv_stage_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : G.obj j) :
    (topologicalDirectColimitIso w).inv
        (topologicalDirectInjection G j x) =
      topologicalDirectInjection F j (w.inv.app j x) := by
  exact congrArg (fun f => f x)
    (topologicalDirectColimitIso_inv_stage w j)

/- Transport a pair of universal maps across a natural isomorphism of
diagrams.  The stage equation is the exact hypothesis needed for the
universal property of the source colimit. -/
@[reassoc]
theorem topologicalDirectColimitIso_hom_comp_descend_eq
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G)
    {X : TopCat.{u}} (fF : topologicalDirectColimit F ⟶ X)
    (fG : topologicalDirectColimit G ⟶ X)
    (h : ∀ j : J,
      w.hom.app j ≫ topologicalDirectInjection G j ≫ fG =
        topologicalDirectInjection F j ≫ fF) :
    (topologicalDirectColimitIso w).hom ≫
        fG = fF := by
  apply colimit.hom_ext
  intro j
  change (topologicalDirectInjection F j ≫
      (topologicalDirectColimitIso w).hom) ≫ fG =
    topologicalDirectInjection F j ≫ fF
  rw [topologicalDirectColimitIso_hom_stage, Category.assoc, h j]

/-- The categorical topological inverse limit of a diagram. -/
noncomputable def topologicalInverseLimit
    (F : J ⥤ TopCat.{u}) : TopCat.{u} :=
  limit F

/-- Canonical continuous projection from a topological inverse limit. -/
noncomputable def topologicalInverseProjection
    (F : J ⥤ TopCat.{u}) (j : J) :
    topologicalInverseLimit F ⟶ F.obj j :=
  limit.π F j

@[reassoc]
theorem topologicalInverseProjection_naturality
    (F : J ⥤ TopCat.{u}) {j k : J} (f : j ⟶ k) :
    topologicalInverseProjection F j ≫ F.map f =
      topologicalInverseProjection F k := by
  exact limit.w F f

theorem topologicalInverseProjection_naturality_apply
    (F : J ⥤ TopCat.{u}) {j k : J} (f : j ⟶ k)
    (x : topologicalInverseLimit F) :
    F.map f (topologicalInverseProjection F j x) =
      topologicalInverseProjection F k x := by
  exact congrArg (fun g => g x)
    (topologicalInverseProjection_naturality F f)

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

theorem topologicalInverseLift_projection_apply
    (F : J ⥤ TopCat.{u}) (c : Cone F) (j : J)
    (x : c.pt) :
    topologicalInverseProjection F j
        (topologicalInverseLift F c x) =
      c.π.app j x := by
  exact congrArg (fun g => g x)
    (topologicalInverseLift_projection F c j)

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

/-- The canonical TopCat isomorphism induced by a natural isomorphism of inverse-limit diagrams. -/
noncomputable def topologicalInverseLimitIso
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    topologicalInverseLimit F ≅ topologicalInverseLimit G :=
  HasLimit.isoOfNatIso w

@[reassoc (attr := simp)]
theorem topologicalInverseLimitIso_hom_projection
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    (topologicalInverseLimitIso w).hom ≫
        topologicalInverseProjection G j =
      topologicalInverseProjection F j ≫ w.hom.app j := by
  exact HasLimit.isoOfNatIso_hom_π w j

@[reassoc (attr := simp)]
theorem topologicalInverseLimitIso_inv_projection
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    (topologicalInverseLimitIso w).inv ≫
        topologicalInverseProjection F j =
      topologicalInverseProjection G j ≫ w.inv.app j := by
  exact HasLimit.isoOfNatIso_inv_π w j

theorem topologicalInverseLimitIso_hom_projection_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : topologicalInverseLimit F) :
    topologicalInverseProjection G j
        ((topologicalInverseLimitIso w).hom x) =
      w.hom.app j (topologicalInverseProjection F j x) := by
  exact congrArg (fun f => f x)
    (topologicalInverseLimitIso_hom_projection w j)

theorem topologicalInverseLimitIso_inv_projection_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : topologicalInverseLimit G) :
    topologicalInverseProjection F j
        ((topologicalInverseLimitIso w).inv x) =
      w.inv.app j (topologicalInverseProjection G j x) := by
  exact congrArg (fun f => f x)
    (topologicalInverseLimitIso_inv_projection w j)

end FilteredColimit.Native.Topological
