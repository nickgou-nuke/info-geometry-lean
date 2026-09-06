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

/-- Native Mathlib `colimit` is used directly. -/
@[reassoc (attr := simp)]
theorem topologicalDirectInjection_naturality
    (F : J ⥤ TopCat.{u}) {j j' : J} (f : j ⟶ j') :
    F.map f ≫ colimit.ι F j' =
      colimit.ι F j := by
  exact colimit.w F f

theorem topologicalDirectInjection_naturality_apply
    (F : J ⥤ TopCat.{u}) {j j' : J} (f : j ⟶ j')
    (x : F.obj j) :
    colimit.ι F j' (F.map f x) =
      colimit.ι F j x := by
  exact congrArg (fun g => g x)
    (topologicalDirectInjection_naturality F f)

/-! ## Natural transformations on direct limits -/

/-- Descend a natural transformation between two diagrams to their direct colimits. -/
noncomputable def topologicalDirectMapBetween
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G) :
    CategoryTheory.Limits.colimit F ⟶ CategoryTheory.Limits.colimit G :=
  colim.map α

@[reassoc (attr := simp)]
theorem topologicalDirectMapBetween_injection
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G) (j : J) :
    colimit.ι F j ≫ topologicalDirectMapBetween α =
      α.app j ≫ colimit.ι G j := by
  exact colimit.ι_map α j

theorem topologicalDirectMapBetween_injection_apply
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G) (j : J)
    (x : F.obj j) :
    topologicalDirectMapBetween α (colimit.ι F j x) =
      colimit.ι G j (α.app j x) := by
  exact congrArg (fun g => g x) (topologicalDirectMapBetween_injection α j)

theorem topologicalDirectMapBetween_id (F : J ⥤ TopCat.{u}) :
    topologicalDirectMapBetween (𝟙 F) = 𝟙 _ := by
  apply colimit.hom_ext
  intro j
  have hmap := topologicalDirectMapBetween_injection (𝟙 F) j
  change colimit.ι F j ≫
      topologicalDirectMapBetween (𝟙 F) =
    colimit.ι F j ≫ 𝟙 _
  change colimit.ι F j ≫
      topologicalDirectMapBetween (𝟙 F) =
    colimit.ι F j ≫ 𝟙 _ at hmap
  exact hmap

theorem topologicalDirectMapBetween_comp
    {F G H : J ⥤ TopCat.{u}} (α : F ⟶ G) (β : G ⟶ H) :
    topologicalDirectMapBetween α ≫ topologicalDirectMapBetween β =
      topologicalDirectMapBetween (α ≫ β) := by
  apply colimit.hom_ext
  intro j
  have hα := topologicalDirectMapBetween_injection α j
  have hβ := topologicalDirectMapBetween_injection β j
  have hαβ := topologicalDirectMapBetween_injection (α ≫ β) j
  change colimit.ι F j ≫
      topologicalDirectMapBetween α ≫ topologicalDirectMapBetween β =
    colimit.ι F j ≫ topologicalDirectMapBetween (α ≫ β)
  calc
    colimit.ι F j ≫
        topologicalDirectMapBetween α ≫ topologicalDirectMapBetween β =
        α.app j ≫ colimit.ι G j ≫
          topologicalDirectMapBetween β := by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ topologicalDirectMapBetween β) hα
    _ = α.app j ≫ β.app j ≫ colimit.ι H j := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ k) hβ
    _ = (α ≫ β).app j ≫ colimit.ι H j := by
          simp only [NatTrans.comp_app, Category.assoc]
    _ = colimit.ι F j ≫
        topologicalDirectMapBetween (α ≫ β) := hαβ.symm

/-- Descend a continuous cocone through the topological direct colimit. -/
@[reassoc]
theorem topologicalDirectDescend_stage
    (F : J ⥤ TopCat.{u}) (c : Cocone F) (j : J) :
    colimit.ι F j ≫ colimit.desc F c =
      c.ι.app j := by
  exact colimit.ι_desc c j

theorem topologicalDirectDescend_stage_apply
    (F : J ⥤ TopCat.{u}) (c : Cocone F) (j : J)
    (x : F.obj j) :
    colimit.desc F c (colimit.ι F j x) =
      c.ι.app j x := by
  exact congrArg (fun g => g x) (topologicalDirectDescend_stage F c j)

/- A dense family of cocone-stage images remains dense after the universal
   map descends from the categorical direct colimit. -/
theorem topologicalDirectDescend_denseRange
    (F : J ⥤ TopCat.{u}) (c : Cocone F)
    (h_dense :
      let stageReadout : (Σ j : J, F.obj j) → c.pt :=
        fun p => (c.ι.app p.1).hom p.2
      Dense (Set.range stageReadout)) :
    DenseRange (colimit.desc F c) := by
  let stageReadout : (Σ j : J, F.obj j) → c.pt :=
    fun p => (c.ι.app p.1).hom p.2
  apply Dense.mono
    (s₁ := Set.range stageReadout)
    (s₂ := Set.range (colimit.desc F c))
  · intro y hy
    rcases hy with ⟨⟨j, x⟩, rfl⟩
    refine ⟨colimit.ι F j x, ?_⟩
    exact congrArg (fun g => g x)
      (topologicalDirectDescend_stage F c j)
  · exact h_dense

/-! Naturality of the universal direct-colimit map with respect to cocone
    descent.  The stage compatibility equation is the only property. -/
theorem topologicalDirectMapBetween_comp_descend_eq
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G) (k : cF.pt ⟶ cG.pt)
    (h : ∀ j : J,
      α.app j ≫ cG.ι.app j = cF.ι.app j ≫ k) :
    topologicalDirectMapBetween α ≫
        colimit.desc G cG =
      colimit.desc F cF ≫ k := by
  apply colimit.hom_ext
  intro j
  have hmap := topologicalDirectMapBetween_injection α j
  have hdescG :
      colimit.ι G j ≫ colimit.desc G cG =
        cG.ι.app j :=
    by exact topologicalDirectDescend_stage G cG j
  have hdescF :
      colimit.ι F j ≫ colimit.desc F cF =
        cF.ι.app j :=
    by exact topologicalDirectDescend_stage F cF j
  change colimit.ι F j ≫
      topologicalDirectMapBetween α ≫
        colimit.desc G cG =
    colimit.ι F j ≫
      colimit.desc F cF ≫ k
  calc
    colimit.ι F j ≫
        topologicalDirectMapBetween α ≫
          colimit.desc G cG =
        α.app j ≫ colimit.ι G j ≫
          colimit.desc G cG := by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ colimit.desc G cG) hmap
    _ = α.app j ≫ cG.ι.app j := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ k) hdescG
    _ = cF.ι.app j ≫ k := h j
    _ = colimit.ι F j ≫
        colimit.desc F cF ≫ k := by
          simpa only [Category.assoc] using
            congrArg (fun q => q ≫ k) (Eq.symm hdescF)

theorem topologicalDirectDescend_unique
    (F : J ⥤ TopCat.{u}) (c : Cocone F)
    (f : CategoryTheory.Limits.colimit F ⟶ c.pt)
    (h : ∀ j : J,
      colimit.ι F j ≫ f = c.ι.app j) :
    f = colimit.desc F c := by
  apply colimit.hom_ext
  intro j
  change colimit.ι F j ≫ f =
    colimit.ι F j ≫ colimit.desc F c
  rw [h j, topologicalDirectDescend_stage]

/-- The canonical TopCat isomorphism induced by a natural isomorphism of diagrams. -/
noncomputable def topologicalDirectColimitIso
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    CategoryTheory.Limits.colimit F ≅ CategoryTheory.Limits.colimit G :=
  HasColimit.isoOfNatIso w

@[reassoc (attr := simp)]
theorem topologicalDirectColimitIso_hom_stage
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    colimit.ι F j ≫
        (topologicalDirectColimitIso w).hom =
      w.hom.app j ≫ colimit.ι G j := by
  exact HasColimit.isoOfNatIso_ι_hom w j

@[reassoc (attr := simp)]
theorem topologicalDirectColimitIso_inv_stage
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    colimit.ι G j ≫
        (topologicalDirectColimitIso w).inv =
      w.inv.app j ≫ colimit.ι F j := by
  exact HasColimit.isoOfNatIso_ι_inv w j

theorem topologicalDirectColimitIso_hom_stage_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : F.obj j) :
    (topologicalDirectColimitIso w).hom
        (colimit.ι F j x) =
      colimit.ι G j (w.hom.app j x) := by
  exact congrArg (fun f => f x)
    (topologicalDirectColimitIso_hom_stage w j)

theorem topologicalDirectColimitIso_inv_stage_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : G.obj j) :
    (topologicalDirectColimitIso w).inv
        (colimit.ι G j x) =
      colimit.ι F j (w.inv.app j x) := by
  exact congrArg (fun f => f x)
    (topologicalDirectColimitIso_inv_stage w j)

/-- The natural-transformation map agrees with the canonical colimit
    isomorphism when the transformation is the forward component of a
    diagram isomorphism. -/
theorem topologicalDirectMapBetween_iso_hom
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    topologicalDirectMapBetween w.hom =
      (topologicalDirectColimitIso w).hom := by
  apply colimit.hom_ext
  intro j
  change colimit.ι F j ≫ topologicalDirectMapBetween w.hom =
    colimit.ι F j ≫ (topologicalDirectColimitIso w).hom
  rw [topologicalDirectMapBetween_injection,
    topologicalDirectColimitIso_hom_stage]

theorem topologicalDirectMapBetween_iso_inv
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    topologicalDirectMapBetween w.inv =
      (topologicalDirectColimitIso w).inv := by
  apply colimit.hom_ext
  intro j
  change colimit.ι G j ≫ topologicalDirectMapBetween w.inv =
    colimit.ι G j ≫ (topologicalDirectColimitIso w).inv
  rw [topologicalDirectMapBetween_injection,
    topologicalDirectColimitIso_inv_stage]

/- Transport a pair of universal maps across a natural isomorphism of
diagrams.  The stage equation is the exact property needed for the
universal property of the source colimit. -/
@[reassoc]
theorem topologicalDirectColimitIso_hom_comp_descend_eq
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G)
    {X : TopCat.{u}} (fF : CategoryTheory.Limits.colimit F ⟶ X)
    (fG : CategoryTheory.Limits.colimit G ⟶ X)
    (h : ∀ j : J,
      w.hom.app j ≫ colimit.ι G j ≫ fG =
        colimit.ι F j ≫ fF) :
    (topologicalDirectColimitIso w).hom ≫
        fG = fF := by
  apply colimit.hom_ext
  intro j
  change (colimit.ι F j ≫
      (topologicalDirectColimitIso w).hom) ≫ fG =
    colimit.ι F j ≫ fF
  rw [topologicalDirectColimitIso_hom_stage, Category.assoc, h j]

@[reassoc]
theorem topologicalInverseProjection_naturality
    (F : J ⥤ TopCat.{u}) {j k : J} (f : j ⟶ k) :
    limit.π F j ≫ F.map f =
      limit.π F k := by
  exact limit.w F f

theorem topologicalInverseProjection_naturality_apply
    (F : J ⥤ TopCat.{u}) {j k : J} (f : j ⟶ k)
    (x : TopCat.carrier (CategoryTheory.Limits.limit F)) :
    F.map f (limit.π F j x) =
      limit.π F k x := by
  exact congrArg (fun g => g x)
    (topologicalInverseProjection_naturality F f)

/-! ## Natural endomorphisms on inverse limits -/

/-- Descend a natural transformation between two diagrams to their inverse limits. -/
noncomputable def topologicalInverseMapBetween
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G) :
    CategoryTheory.Limits.limit F ⟶ CategoryTheory.Limits.limit G :=
  lim.map α

@[reassoc (attr := simp)]
theorem topologicalInverseMapBetween_projection
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G) (j : J) :
    topologicalInverseMapBetween α ≫ limit.π G j =
      limit.π F j ≫ α.app j := by
  exact IsLimit.map_π (limit.cone F) (limit.isLimit G) α j

theorem topologicalInverseMapBetween_projection_apply
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G) (j : J)
    (x : TopCat.carrier (CategoryTheory.Limits.limit F)) :
    limit.π G j (topologicalInverseMapBetween α x) =
      α.app j (limit.π F j x) := by
  exact congrArg (fun g => g x) (topologicalInverseMapBetween_projection α j)

/-- Descend a natural endomorphism to the native topological inverse limit. -/
noncomputable def topologicalInverseMap
    (F : J ⥤ TopCat.{u}) (α : F ⟶ F) :
    CategoryTheory.Limits.limit F ⟶ CategoryTheory.Limits.limit F :=
  lim.map α

@[reassoc (attr := simp)]
theorem topologicalInverseMap_projection
    (F : J ⥤ TopCat.{u}) (α : F ⟶ F) (j : J) :
    topologicalInverseMap F α ≫ limit.π F j =
      limit.π F j ≫ α.app j := by
  exact IsLimit.map_π (limit.cone F) (limit.isLimit F) α j

theorem topologicalInverseMap_projection_apply
    (F : J ⥤ TopCat.{u}) (α : F ⟶ F) (j : J)
    (x : TopCat.carrier (CategoryTheory.Limits.limit F)) :
    limit.π F j (topologicalInverseMap F α x) =
      α.app j (limit.π F j x) := by
  exact congrArg (fun g => g x) (topologicalInverseMap_projection F α j)

theorem topologicalInverseMap_id (F : J ⥤ TopCat.{u}) :
    topologicalInverseMap F (𝟙 F) = 𝟙 _ := by
  apply limit.hom_ext
  intro j
  have hmap := topologicalInverseMap_projection F (𝟙 F) j
  change topologicalInverseMap F (𝟙 F) ≫ limit.π F j =
      limit.π F j ≫ 𝟙 _ at hmap
  change topologicalInverseMap F (𝟙 F) ≫ limit.π F j =
      𝟙 _ ≫ limit.π F j
  simpa only [Category.comp_id, Category.id_comp] using hmap

theorem topologicalInverseMap_comp
    (F : J ⥤ TopCat.{u}) (α β : F ⟶ F) :
    topologicalInverseMap F α ≫ topologicalInverseMap F β =
      topologicalInverseMap F (α ≫ β) := by
  apply limit.hom_ext
  intro j
  have hα := topologicalInverseMap_projection F α j
  have hβ := topologicalInverseMap_projection F β j
  have hαβ := topologicalInverseMap_projection F (α ≫ β) j
  change topologicalInverseMap F α ≫ limit.π F j =
      limit.π F j ≫ α.app j at hα
  change topologicalInverseMap F β ≫ limit.π F j =
      limit.π F j ≫ β.app j at hβ
  change topologicalInverseMap F (α ≫ β) ≫ limit.π F j =
      limit.π F j ≫ (α ≫ β).app j at hαβ
  change topologicalInverseMap F α ≫ topologicalInverseMap F β ≫
      limit.π F j = topologicalInverseMap F (α ≫ β) ≫ limit.π F j
  calc
    topologicalInverseMap F α ≫ topologicalInverseMap F β ≫
        limit.π F j =
        topologicalInverseMap F α ≫
          (limit.π F j ≫ β.app j) := by
            simpa only [Category.assoc] using
              congrArg (fun k => topologicalInverseMap F α ≫ k) hβ
    _ = (topologicalInverseMap F α ≫ limit.π F j) ≫ β.app j := by
          simp only [Category.assoc]
    _ = (limit.π F j ≫ α.app j) ≫ β.app j := by rw [hα]
    _ = limit.π F j ≫ (α ≫ β).app j := by
          simp only [Category.assoc, NatTrans.comp_app]
    _ = topologicalInverseMap F (α ≫ β) ≫ limit.π F j := hαβ.symm

theorem topologicalInverseMap_involutive
    (F : J ⥤ TopCat.{u}) (α : F ⟶ F)
    (hα : ∀ j : J, α.app j ≫ α.app j = 𝟙 _) :
    topologicalInverseMap F α ≫ topologicalInverseMap F α = 𝟙 _ := by
  apply limit.hom_ext
  intro j
  let m := topologicalInverseMap F α
  let p := limit.π F j
  have hp : m ≫ p = p ≫ α.app j :=
    topologicalInverseMap_projection F α j
  change m ≫ m ≫ p = 𝟙 _ ≫ p
  calc
    m ≫ m ≫ p = m ≫ (p ≫ α.app j) := by
      simpa only [Category.assoc] using
        congrArg (fun k => m ≫ k) hp
    _ = (m ≫ p) ≫ α.app j := by simp only [Category.assoc]
    _ = (p ≫ α.app j) ≫ α.app j := by rw [hp]
    _ = p := by simp only [Category.assoc, hα j, Category.comp_id]

theorem topologicalInverseMap_artin_relation
    (F : J ⥤ TopCat.{u}) (α β : F ⟶ F)
    (hartin : ∀ j : J,
      α.app j ≫ β.app j ≫ α.app j =
        β.app j ≫ α.app j ≫ β.app j) :
    topologicalInverseMap F α ≫ topologicalInverseMap F β ≫
        topologicalInverseMap F α =
      topologicalInverseMap F β ≫ topologicalInverseMap F α ≫
        topologicalInverseMap F β := by
  apply limit.hom_ext
  intro j
  let mα := topologicalInverseMap F α
  let mβ := topologicalInverseMap F β
  let p := limit.π F j
  have hαj : mα ≫ p = p ≫ α.app j :=
    topologicalInverseMap_projection F α j
  have hβj : mβ ≫ p = p ≫ β.app j :=
    topologicalInverseMap_projection F β j
  change mα ≫ mβ ≫ mα ≫ p = mβ ≫ mα ≫ mβ ≫ p
  calc
    mα ≫ mβ ≫ mα ≫ p = mα ≫ mβ ≫ (p ≫ α.app j) := by
      simpa only [Category.assoc] using
        congrArg (fun k => mα ≫ mβ ≫ k) hαj
    _ = mα ≫ (p ≫ β.app j) ≫ α.app j := by
      simpa only [Category.assoc] using
        congrArg (fun k => mα ≫ k ≫ α.app j) hβj
    _ = (p ≫ α.app j) ≫ β.app j ≫ α.app j := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ β.app j ≫ α.app j) hαj
    _ = p ≫ α.app j ≫ β.app j ≫ α.app j := by
      simp only [Category.assoc]
    _ = p ≫ β.app j ≫ α.app j ≫ β.app j := by
      rw [hartin j]
    _ = (p ≫ β.app j) ≫ α.app j ≫ β.app j := by
      simp only [Category.assoc]
    _ = (mβ ≫ p) ≫ α.app j ≫ β.app j := by
      rw [hβj]
    _ = mβ ≫ (p ≫ α.app j) ≫ β.app j := by
      simp only [Category.assoc]
    _ = mβ ≫ mα ≫ (p ≫ β.app j) := by
      simpa only [Category.assoc] using
        congrArg (fun k => mβ ≫ k ≫ β.app j) hαj.symm
    _ = mβ ≫ mα ≫ mβ ≫ p := by
      simpa only [Category.assoc] using
        congrArg (fun k => mβ ≫ mα ≫ k) hβj.symm

/-- Lift a compatible continuous cone into a topological inverse limit. -/
@[reassoc]
theorem topologicalInverseLift_projection
    (F : J ⥤ TopCat.{u}) (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j =
      c.π.app j := by
  exact limit.lift_π c j

theorem topologicalInverseLift_projection_apply
    (F : J ⥤ TopCat.{u}) (c : Cone F) (j : J)
    (x : c.pt) :
    limit.π F j
        (limit.lift F c x) =
      c.π.app j x := by
  exact congrArg (fun g => g x)
    (topologicalInverseLift_projection F c j)

/-! Dual naturality statement for a cone lift followed by the universal
    inverse-limit map. -/
theorem topologicalInverseLift_mapBetween_eq
    {F G : J ⥤ TopCat.{u}} (α : F ⟶ G)
    (cF : Cone F) (cG : Cone G) (k : cF.pt ⟶ cG.pt)
    (h : ∀ j : J,
      cF.π.app j ≫ α.app j = k ≫ cG.π.app j) :
    limit.lift F cF ≫
        topologicalInverseMapBetween α =
      k ≫ limit.lift G cG := by
  apply limit.hom_ext
  intro j
  have hmap := topologicalInverseMapBetween_projection α j
  have hF := topologicalInverseLift_projection F cF j
  have hG := topologicalInverseLift_projection G cG j
  change (limit.lift F cF ≫
      topologicalInverseMapBetween α) ≫
      limit.π G j =
    k ≫ limit.lift G cG ≫
      limit.π G j
  calc
    (limit.lift F cF ≫
        topologicalInverseMapBetween α) ≫
        limit.π G j =
      limit.lift F cF ≫
        (limit.π F j ≫ α.app j) := by
          simpa only [Category.assoc] using
            congrArg (fun k => limit.lift F cF ≫ k) hmap
    _ = (limit.lift F cF ≫
        limit.π F j) ≫ α.app j := by
          simp only [Category.assoc]
    _ = cF.π.app j ≫ α.app j := by rw [hF]
    _ = k ≫ cG.π.app j := h j
    _ = k ≫ limit.lift G cG ≫
        limit.π G j := by
          simpa only [Category.assoc] using
            congrArg (fun q => k ≫ q) hG.symm

theorem topologicalInverseLift_unique
    (F : J ⥤ TopCat.{u}) (c : Cone F)
    (f : c.pt ⟶ CategoryTheory.Limits.limit F)
    (h : ∀ j : J,
      f ≫ limit.π F j = c.π.app j) :
    f = limit.lift F c := by
  apply limit.hom_ext
  intro j
  change f ≫ limit.π F j =
    limit.lift F c ≫ limit.π F j
  rw [h j, topologicalInverseLift_projection]

/-- The canonical TopCat isomorphism induced by a natural isomorphism of inverse-limit diagrams. -/
noncomputable def topologicalInverseLimitIso
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    CategoryTheory.Limits.limit F ≅ CategoryTheory.Limits.limit G :=
  HasLimit.isoOfNatIso w

@[reassoc (attr := simp)]
theorem topologicalInverseLimitIso_hom_projection
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    (topologicalInverseLimitIso w).hom ≫
        limit.π G j =
      limit.π F j ≫ w.hom.app j := by
  exact HasLimit.isoOfNatIso_hom_π w j

@[reassoc (attr := simp)]
theorem topologicalInverseLimitIso_inv_projection
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J) :
    (topologicalInverseLimitIso w).inv ≫
        limit.π F j =
      limit.π G j ≫ w.inv.app j := by
  exact HasLimit.isoOfNatIso_inv_π w j

theorem topologicalInverseLimitIso_hom_projection_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : TopCat.carrier (CategoryTheory.Limits.limit F)) :
    limit.π G j
        ((topologicalInverseLimitIso w).hom x) =
      w.hom.app j (limit.π F j x) := by
  exact congrArg (fun f => f x)
    (topologicalInverseLimitIso_hom_projection w j)

theorem topologicalInverseLimitIso_inv_projection_apply
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : TopCat.carrier (CategoryTheory.Limits.limit G)) :
    limit.π F j
        ((topologicalInverseLimitIso w).inv x) =
      w.inv.app j (limit.π G j x) := by
  exact congrArg (fun f => f x)
    (topologicalInverseLimitIso_inv_projection w j)

/- Transport universal maps into inverse limits across a natural
   isomorphism of diagrams. -/
theorem topologicalInverseLimitIso_hom_comp_eq
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G)
    {X : TopCat.{u}} (fF : X ⟶ CategoryTheory.Limits.limit F)
    (fG : X ⟶ CategoryTheory.Limits.limit G)
    (h : ∀ j : J,
      fG ≫ limit.π G j =
        fF ≫ limit.π F j ≫ w.hom.app j) :
    fF ≫ (topologicalInverseLimitIso w).hom = fG := by
  apply limit.hom_ext
  intro j
  calc
    (fF ≫ (topologicalInverseLimitIso w).hom) ≫
        limit.π G j =
        fF ≫ ((topologicalInverseLimitIso w).hom ≫
          limit.π G j) := by
            simp only [Category.assoc]
    _ = fF ≫ (limit.π F j ≫ w.hom.app j) := by
          rw [topologicalInverseLimitIso_hom_projection]
    _ = fG ≫ limit.π G j := by
          rw [← h j]
    _ = fG ≫ limit.π G j := rfl

theorem topologicalInverseLimitIso_inv_comp_eq
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G)
    {X : TopCat.{u}} (fF : X ⟶ CategoryTheory.Limits.limit F)
    (fG : X ⟶ CategoryTheory.Limits.limit G)
    (h : ∀ j : J,
      fF ≫ limit.π F j =
        fG ≫ limit.π G j ≫ w.inv.app j) :
    fG ≫ (topologicalInverseLimitIso w).inv = fF := by
  apply limit.hom_ext
  intro j
  calc
    (fG ≫ (topologicalInverseLimitIso w).inv) ≫
        limit.π F j =
        fG ≫ ((topologicalInverseLimitIso w).inv ≫
          limit.π F j) := by
            simp only [Category.assoc]
    _ = fG ≫ (limit.π G j ≫ w.inv.app j) := by
          rw [topologicalInverseLimitIso_inv_projection]
    _ = fF ≫ limit.π F j := by
          rw [← h j]
    _ = fF ≫ limit.π F j := rfl

/-- The inverse-limit map agrees with the canonical limit isomorphism for
    either component of a diagram isomorphism. -/
theorem topologicalInverseMapBetween_iso_hom
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    topologicalInverseMapBetween w.hom =
      (topologicalInverseLimitIso w).hom := by
  apply limit.hom_ext
  intro j
  change topologicalInverseMapBetween w.hom ≫
      limit.π G j =
    (topologicalInverseLimitIso w).hom ≫
      limit.π G j
  rw [topologicalInverseMapBetween_projection,
    topologicalInverseLimitIso_hom_projection]

theorem topologicalInverseMapBetween_iso_inv
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    topologicalInverseMapBetween w.inv =
      (topologicalInverseLimitIso w).inv := by
  apply limit.hom_ext
  intro j
  change topologicalInverseMapBetween w.inv ≫
      limit.π F j =
    (topologicalInverseLimitIso w).inv ≫
      limit.π F j
  rw [topologicalInverseMapBetween_projection,
    topologicalInverseLimitIso_inv_projection]

end FilteredColimit.Native.Topological
