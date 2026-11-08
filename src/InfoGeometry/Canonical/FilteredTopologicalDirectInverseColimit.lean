/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native topological direct and inverse colimit interfaces

This owner exposes the categorical universal properties in `TopCat` directly.
The constructions are the Mathlib `colimit` and `limit`; no replacement by a
sequence, coordinate chart, metric epsilon argument, or finite enumeration is
made.  The stage laws below are the exact continuous-map equations supplied
by the universal properties.

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
- **BUCKET 1 (Genuine Constructive Theorems)**:
  - `topologicalDirectColimit`, `topologicalDirectInjection`,
    `topologicalDirectInjection_naturality`, `topologicalDirectInjection_naturality_apply`
  - `topologicalDirectDescend`, `topologicalDirectDescend_stage`,
    `topologicalDirectDescend_stage_apply`, `topologicalDirectDescend_unique`
  - `topologicalDirectColimitIso`, `topologicalDirectColimitIso_hom_stage`,
    `topologicalDirectColimitIso_inv_stage`, `topologicalDirectColimitIso_hom_stage_apply`,
    `topologicalDirectColimitIso_inv_stage_apply`, `topologicalDirectColimitIso_hom_comp_descend_eq`
  - `topologicalInverseLimit`, `topologicalInverseProjection`,
    `topologicalInverseProjection_naturality`, `topologicalInverseProjection_naturality_apply`
  - `topologicalInverseLift`, `topologicalInverseLift_projection`,
    `topologicalInverseLift_projection_apply`, `topologicalInverseLift_unique`
  - `topologicalInverseLimitIso`, `topologicalInverseLimitIso_hom_projection`,
    `topologicalInverseLimitIso_inv_projection`, `topologicalInverseLimitIso_hom_projection_apply`,
    `topologicalInverseLimitIso_inv_projection_apply`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None (all results are polymorphic over `J : Type u`).
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` wrapper structures.
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

/-- Naturality of the canonical stage injections into `topologicalDirectColimit F`. -/
@[reassoc (attr := simp)]
theorem topologicalDirectInjection_naturality
    (F : J ⥤ TopCat.{u}) {j j' : J} (f : j ⟶ j') :
    F.map f ≫ topologicalDirectInjection F j' =
      topologicalDirectInjection F j := by
  have h := colimit.w F f
  exact h

/-- Pointwise evaluation of `topologicalDirectInjection_naturality`. -/
theorem topologicalDirectInjection_naturality_apply
    (F : J ⥤ TopCat.{u}) {j j' : J} (f : j ⟶ j')
    (x : F.obj j) :
    topologicalDirectInjection F j' (F.map f x) =
      topologicalDirectInjection F j x := by
  have h := topologicalDirectInjection_naturality F f
  exact congrArg (fun g => g x) h

/-- Descend a continuous cocone through the topological direct colimit. -/
noncomputable def topologicalDirectDescend
    (F : J ⥤ TopCat.{u}) (c : Cocone F) :
    topologicalDirectColimit F ⟶ c.pt :=
  colimit.desc F c

/-- Factoring `topologicalDirectDescend F c` through the `j`-th stage injection recovers `c.ι.app j`. -/
@[reassoc]
theorem topologicalDirectDescend_stage
    (F : J ⥤ TopCat.{u}) (c : Cocone F) (j : J) :
    topologicalDirectInjection F j ≫ topologicalDirectDescend F c =
      c.ι.app j := by
  have h := colimit.ι_desc c j
  exact h

/-- Pointwise evaluation of `topologicalDirectDescend_stage`. -/
theorem topologicalDirectDescend_stage_apply
    (F : J ⥤ TopCat.{u}) (c : Cocone F) (j : J)
    (x : F.obj j) :
    topologicalDirectDescend F c (topologicalDirectInjection F j x) =
      c.ι.app j x := by
  have h := topologicalDirectDescend_stage F c j
  exact congrArg (fun g => g x) h

/-- Uniqueness of the descended continuous map out of `topologicalDirectColimit F`. -/
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

/-- Forward stage compatibility for `topologicalDirectColimitIso w`. -/
@[reassoc (attr := simp)]
theorem topologicalDirectColimitIso_hom_stage
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    topologicalDirectInjection F j ≫
        (topologicalDirectColimitIso w).hom =
      w.hom.app j ≫ topologicalDirectInjection G j := by
  have h := HasColimit.isoOfNatIso_ι_hom w j
  exact h

/-- Inverse stage compatibility for `topologicalDirectColimitIso w`. -/
@[reassoc (attr := simp)]
theorem topologicalDirectColimitIso_inv_stage
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    topologicalDirectInjection G j ≫
        (topologicalDirectColimitIso w).inv =
      w.inv.app j ≫ topologicalDirectInjection F j := by
  have h := HasColimit.isoOfNatIso_ι_inv w j
  exact h

/-- Pointwise evaluation of `topologicalDirectColimitIso_hom_stage`. -/
theorem topologicalDirectColimitIso_hom_stage_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : F.obj j) :
    (topologicalDirectColimitIso w).hom
        (topologicalDirectInjection F j x) =
      topologicalDirectInjection G j (w.hom.app j x) := by
  have h := topologicalDirectColimitIso_hom_stage w j
  exact congrArg (fun f => f x) h

/-- Pointwise evaluation of `topologicalDirectColimitIso_inv_stage`. -/
theorem topologicalDirectColimitIso_inv_stage_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : G.obj j) :
    (topologicalDirectColimitIso w).inv
        (topologicalDirectInjection G j x) =
      topologicalDirectInjection F j (w.inv.app j x) := by
  have h := topologicalDirectColimitIso_inv_stage w j
  exact congrArg (fun f => f x) h

/-- Transport a pair of universal maps across a natural isomorphism of
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

/-- Naturality of the canonical stage projections from `topologicalInverseLimit F`. -/
@[reassoc]
theorem topologicalInverseProjection_naturality
    (F : J ⥤ TopCat.{u}) {j k : J} (f : j ⟶ k) :
    topologicalInverseProjection F j ≫ F.map f =
      topologicalInverseProjection F k := by
  have h := limit.w F f
  exact h

/-- Pointwise evaluation of `topologicalInverseProjection_naturality`. -/
theorem topologicalInverseProjection_naturality_apply
    (F : J ⥤ TopCat.{u}) {j k : J} (f : j ⟶ k)
    (x : topologicalInverseLimit F) :
    F.map f (topologicalInverseProjection F j x) =
      topologicalInverseProjection F k x := by
  have h := topologicalInverseProjection_naturality F f
  exact congrArg (fun g => g x) h

/-- Lift a compatible continuous cone into a topological inverse limit. -/
noncomputable def topologicalInverseLift
    (F : J ⥤ TopCat.{u}) (c : Cone F) :
    c.pt ⟶ topologicalInverseLimit F :=
  limit.lift F c

/-- Composing `topologicalInverseLift F c` with the `j`-th stage projection recovers `c.π.app j`. -/
@[reassoc]
theorem topologicalInverseLift_projection
    (F : J ⥤ TopCat.{u}) (c : Cone F) (j : J) :
    topologicalInverseLift F c ≫ topologicalInverseProjection F j =
      c.π.app j := by
  have h := limit.lift_π c j
  exact h

/-- Pointwise evaluation of `topologicalInverseLift_projection`. -/
theorem topologicalInverseLift_projection_apply
    (F : J ⥤ TopCat.{u}) (c : Cone F) (j : J)
    (x : c.pt) :
    topologicalInverseProjection F j
        (topologicalInverseLift F c x) =
      c.π.app j x := by
  have h := topologicalInverseLift_projection F c j
  exact congrArg (fun g => g x) h

/-- Uniqueness of the lifted continuous map into `topologicalInverseLimit F`. -/
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

/-- Forward projection compatibility for `topologicalInverseLimitIso w`. -/
@[reassoc (attr := simp)]
theorem topologicalInverseLimitIso_hom_projection
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    (topologicalInverseLimitIso w).hom ≫
        topologicalInverseProjection G j =
      topologicalInverseProjection F j ≫ w.hom.app j := by
  have h := HasLimit.isoOfNatIso_hom_π w j
  exact h

/-- Inverse projection compatibility for `topologicalInverseLimitIso w`. -/
@[reassoc (attr := simp)]
theorem topologicalInverseLimitIso_inv_projection
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    (topologicalInverseLimitIso w).inv ≫
        topologicalInverseProjection F j =
      topologicalInverseProjection G j ≫ w.inv.app j := by
  have h := HasLimit.isoOfNatIso_inv_π w j
  exact h

/-- Pointwise evaluation of `topologicalInverseLimitIso_hom_projection`. -/
theorem topologicalInverseLimitIso_hom_projection_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : topologicalInverseLimit F) :
    topologicalInverseProjection G j
        ((topologicalInverseLimitIso w).hom x) =
      w.hom.app j (topologicalInverseProjection F j x) := by
  have h := topologicalInverseLimitIso_hom_projection w j
  exact congrArg (fun f => f x) h

/-- Pointwise evaluation of `topologicalInverseLimitIso_inv_projection`. -/
theorem topologicalInverseLimitIso_inv_projection_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : topologicalInverseLimit G) :
    topologicalInverseProjection F j
        ((topologicalInverseLimitIso w).inv x) =
      w.inv.app j (topologicalInverseProjection G j x) := by
  have h := topologicalInverseLimitIso_inv_projection w j
  exact congrArg (fun f => f x) h

end FilteredColimit.Native.Topological
