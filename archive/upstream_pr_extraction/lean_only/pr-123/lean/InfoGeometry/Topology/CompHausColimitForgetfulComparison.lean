import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausColimit

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

noncomputable def compHausTopColimit
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] : CompHaus :=
  CompHaus.of ((colimit (F ⋙ compHausToTop) : TopCat) : Type)

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
      simpa using congrArg (fun h => h x)
        (colimit.w (F ⋙ compHausToTop) f)

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
  exact ⟨topColimitToCompHausColimit F⟩

theorem topColimitToCompHausColimitCompHaus_forget
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)] :
    compHausToTop.map (topColimitToCompHausColimitCompHaus F) =
      topColimitToCompHausColimit F :=
  rfl

theorem compHausColimitToTopColimit_stage
    (F : J ⥤ CompHaus)
    [CompactSpace ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    [T2Space ((colimit (F ⋙ compHausToTop) : TopCat) : Type)]
    (j : J) :
    compHausToTop.map (colimit.ι F j) ≫
        compHausToTop.map (compHausColimitToTopColimit F) =
      colimit.ι (F ⋙ compHausToTop) j := by
  change
    compHausToTop.map (colimit.ι F j) ≫
        compHausToTop.map (colimit.desc F
          (compHausColimitToTopColimitCocone F)) =
      colimit.ι (F ⋙ compHausToTop) j
  rw [← compHausToTop.map_comp, colimit.ι_desc]
  rfl

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
  simp only [compHausToTop.map_comp, compHausToTop.map_id]
  rw [topColimitToCompHausColimitCompHaus_forget]
  rw [← Category.assoc,
    compHausColimitToTopColimit_stage,
    topColimitToCompHausColimit_stage]
  simp

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
  simp only [compHausToTop.map_comp, compHausToTop.map_id]
  rw [topColimitToCompHausColimitCompHaus_forget]
  apply colimit.hom_ext
  intro j
  rw [← Category.assoc, topColimitToCompHausColimit_stage,
    compHausColimitToTopColimit_stage]
  exact (Category.comp_id _).symm

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
