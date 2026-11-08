import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Forgetful comparison for compact-Hausdorff colimits

The forgetful functor `CompHaus ⥤ TopCat` is not used here as if it
preserved colimits automatically.  When the TopCat colimit of the forgotten
diagram is explicitly known to be compact and Hausdorff, the two universal
properties give a canonical isomorphism.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

variable {J : Type} [Category J]

noncomputable abbrev compHausTopColimit
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] : CompHaus :=
  CompHaus.of ((colimit (F ⋙ compHausToTop) : TopCat) : Type)

theorem compHausTopColimit_forget
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    compHausToTop.obj (compHausTopColimit F) = colimit (F ⋙ compHausToTop) :=
  rfl

noncomputable def compHausColimitToTopColimitCocone
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    Cocone F where
  pt := compHausTopColimit F
  ι := by
    refine { app := ?_, naturality := ?_ }
    · intro j
      exact ⟨colimit.ι (F ⋙ compHausToTop) j⟩
    · intro j k f
      apply ConcreteCategory.hom_ext
      intro x
      change
        (colimit.ι (F ⋙ compHausToTop) k)
            ((F.map f) x) =
          (colimit.ι (F ⋙ compHausToTop) j) x
      let xTop : (F ⋙ compHausToTop).obj j := x
      have hw := congrArg
        (fun h : (F ⋙ compHausToTop).obj j ⟶
          colimit (F ⋙ compHausToTop) => h xTop)
        (colimit.w (F ⋙ compHausToTop) f)
      rw [CategoryTheory.comp_apply] at hw
      change (colimit.ι (F ⋙ compHausToTop) k) ((F.map f) x) =
        (colimit.ι (F ⋙ compHausToTop) j) x at hw
      exact hw

/-- The forgotten compact-Hausdorff colimit is identified with the TopCat
colimit object by the carrier equality. -/
noncomputable def compHausTopColimitForgetIso
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    compHausToTop.obj (compHausTopColimit F) ≅
      colimit (F ⋙ compHausToTop) :=
  eqToIso (compHausTopColimit_forget F)

noncomputable def compHausColimitToTopColimit
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    colimit F ⟶ compHausTopColimit F :=
  colimit.desc F (compHausColimitToTopColimitCocone F)

noncomputable def topColimitToCompHausColimitCocone
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    Cocone (F ⋙ compHausToTop) where
  pt := compHausToTop.obj (colimit F)
  ι := by
    refine { app := ?_, naturality := ?_ }
    · intro j
      exact compHausToTop.map (colimit.ι F j)
    · intro j k f
      change
        compHausToTop.map (F.map f) ≫
            compHausToTop.map (colimit.ι F k) =
          compHausToTop.map (colimit.ι F j)
      rw [← compHausToTop.map_comp]
      exact congrArg (fun h => compHausToTop.map h)
        (colimit.w F f)

noncomputable def topColimitToCompHausColimit
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    (colimit (F ⋙ compHausToTop) : TopCat) ⟶
      compHausToTop.obj (colimit F) :=
  colimit.desc (F ⋙ compHausToTop)
    (topColimitToCompHausColimitCocone F)

noncomputable def topColimitToCompHausColimitCompHaus
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    compHausTopColimit F ⟶ colimit F := by
  exact compHausToTop.preimage
    ((compHausTopColimitForgetIso F).hom ≫
      topColimitToCompHausColimit F)

theorem topColimitToCompHausColimitCompHaus_forget
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    compHausToTop.map (topColimitToCompHausColimitCompHaus F) =
      (compHausTopColimitForgetIso F).hom ≫
        topColimitToCompHausColimit F :=
  compHausToTop.map_preimage _

theorem compHausColimitToTopColimit_stage
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    (j : J) :
    compHausToTop.map (colimit.ι F j) ≫
        compHausToTop.map (compHausColimitToTopColimit F) =
      colimit.ι (F ⋙ compHausToTop) j ≫
        (compHausTopColimitForgetIso F).inv := by
  rw [← compHausToTop.map_comp]
  have h := congrArg compHausToTop.map
    (colimit.ι_desc (compHausColimitToTopColimitCocone F) j)
  rw [compHausToTop.map_comp] at h
  change compHausToTop.map (colimit.ι F j) ≫
      compHausToTop.map (compHausColimitToTopColimit F) =
    colimit.ι (F ⋙ compHausToTop) j ≫
      (compHausTopColimitForgetIso F).inv at h
  exact h

theorem topColimitToCompHausColimit_stage
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    (j : J) :
    colimit.ι (F ⋙ compHausToTop) j ≫
        topColimitToCompHausColimit F =
      compHausToTop.map (colimit.ι F j) :=
  colimit.ι_desc (topColimitToCompHausColimitCocone F) j

theorem compHausColimitForgetfulComparison_hom_inv_id
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    compHausColimitToTopColimit F ≫
        topColimitToCompHausColimitCompHaus F =
      𝟙 _ := by
  apply colimit.hom_ext
  intro j
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simp only [Functor.map_comp, compHausToTop.map_id]
  rw [topColimitToCompHausColimitCompHaus_forget]
  calc
    (compHausToTop.map (colimit.ι F j) ≫
        compHausToTop.map (compHausColimitToTopColimit F)) ≫
        (compHausTopColimitForgetIso F).hom ≫
        topColimitToCompHausColimit F =
      colimit.ι (F ⋙ compHausToTop) j ≫
        (compHausTopColimitForgetIso F).inv ≫
        (compHausTopColimitForgetIso F).hom ≫
        topColimitToCompHausColimit F := by
          exact congrArg
            (fun f => f ≫ (compHausTopColimitForgetIso F).hom ≫
              topColimitToCompHausColimit F)
            (compHausColimitToTopColimit_stage F j)
    _ = compHausToTop.map (colimit.ι F j) := by
      rw [Iso.inv_hom_id_assoc]
      exact topColimitToCompHausColimit_stage F j

theorem compHausColimitForgetfulComparison_inv_hom_id
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    topColimitToCompHausColimitCompHaus F ≫
        compHausColimitToTopColimit F =
      𝟙 _ := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simp only [Functor.map_comp, compHausToTop.map_id]
  rw [topColimitToCompHausColimitCompHaus_forget]
  have h :
      (compHausTopColimitForgetIso F).inv ≫
          ((compHausTopColimitForgetIso F).hom ≫
            topColimitToCompHausColimit F) ≫
            compHausToTop.map (compHausColimitToTopColimit F) =
        (compHausTopColimitForgetIso F).inv := by
    apply colimit.hom_ext
    intro j
    calc
      colimit.ι (F ⋙ compHausToTop) j ≫
          (compHausTopColimitForgetIso F).inv ≫
          ((compHausTopColimitForgetIso F).hom ≫
            topColimitToCompHausColimit F) ≫
            compHausToTop.map (compHausColimitToTopColimit F) =
        colimit.ι (F ⋙ compHausToTop) j ≫
          topColimitToCompHausColimit F ≫
          compHausToTop.map (compHausColimitToTopColimit F) := by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = compHausToTop.map (colimit.ι F j) ≫
          compHausToTop.map (compHausColimitToTopColimit F) := by
            exact congrArg
              (fun f => f ≫ compHausToTop.map (compHausColimitToTopColimit F))
              (topColimitToCompHausColimit_stage F j)
      _ = colimit.ι (F ⋙ compHausToTop) j ≫
          (compHausTopColimitForgetIso F).inv :=
            compHausColimitToTopColimit_stage F j
  have h' := congrArg
    (fun f => (compHausTopColimitForgetIso F).hom ≫ f) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id] using h'

noncomputable def compHausColimitForgetfulComparison
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    colimit F ≅ compHausTopColimit F :=
  { hom := compHausColimitToTopColimit F
    inv := topColimitToCompHausColimitCompHaus F
    hom_inv_id := compHausColimitForgetfulComparison_hom_inv_id F
    inv_hom_id := compHausColimitForgetfulComparison_inv_hom_id F }

end InfoGeometry.Topology
