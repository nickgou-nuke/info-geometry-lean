import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausIndexed

/-!
# Colimits of compact-Hausdorff varying-carrier quotients

The quotient functor and its indexed quotient/range isomorphism already live
in `CompHaus`.  This owner supplies the corresponding colimit object, stage
maps, functorial maps between colimits, and the canonical colimit isomorphism
to the observation-range diagram.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausColimit
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) : CompHaus :=
  colimit (compactIndexedObservationQuotientDiagram D)

noncomputable def compactIndexedObservationQuotientCompHausColimitStage
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) (j : J) :
    (compactIndexedObservationQuotientDiagram D).obj j ⟶
      compactIndexedObservationQuotientCompHausColimit D :=
  colimit.ι (compactIndexedObservationQuotientDiagram D) j

noncomputable def compactIndexedObservationQuotientCompHausMappedNatTrans
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationQuotientDiagram D ⟶
      compactIndexedObservationQuotientDiagram E where
  app j := compactSymbolicLatentObservationQuotientCompHausFunctor.map
    (τ.app j)
  naturality := by
    intro j k f
    change
      compactSymbolicLatentObservationQuotientCompHausFunctor.map (D.map f) ≫
          compactSymbolicLatentObservationQuotientCompHausFunctor.map
            (τ.app k) =
        compactSymbolicLatentObservationQuotientCompHausFunctor.map
            (τ.app j) ≫
          compactSymbolicLatentObservationQuotientCompHausFunctor.map
            (E.map f)
    rw [← compactSymbolicLatentObservationQuotientCompHausFunctor.map_comp,
      ← compactSymbolicLatentObservationQuotientCompHausFunctor.map_comp,
      τ.naturality]

noncomputable def compactIndexedObservationQuotientCompHausColimitMap
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationQuotientCompHausColimit D ⟶
      compactIndexedObservationQuotientCompHausColimit E :=
  colim.map (compactIndexedObservationQuotientCompHausMappedNatTrans τ)

theorem compactIndexedObservationQuotientCompHausColimitStage_map
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (j : J) :
    compactIndexedObservationQuotientCompHausColimitStage D j ≫
        compactIndexedObservationQuotientCompHausColimitMap τ =
      (compactIndexedObservationQuotientCompHausMappedNatTrans τ).app j ≫
        compactIndexedObservationQuotientCompHausColimitStage E j :=
  colimit.ι_map (compactIndexedObservationQuotientCompHausMappedNatTrans τ) j

theorem compactIndexedObservationQuotientCompHausColimitMap_id
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationQuotientCompHausColimitMap (𝟙 D) = 𝟙 _ := by
  apply colimit.hom_ext
  intro j
  change
    colimit.ι (compactIndexedObservationQuotientDiagram D) j ≫
        colim.map (compactIndexedObservationQuotientCompHausMappedNatTrans (𝟙 D)) =
      colimit.ι (compactIndexedObservationQuotientDiagram D) j ≫ 𝟙 _
  rw [colimit.ι_map]
  change
    compactSymbolicLatentObservationQuotientCompHausFunctor.map (𝟙 (D.obj j)) ≫
        colimit.ι (compactIndexedObservationQuotientDiagram D) j =
      colimit.ι (compactIndexedObservationQuotientDiagram D) j
  rw [compactSymbolicLatentObservationQuotientCompHausFunctor.map_id,
    Category.id_comp]

theorem compactIndexedObservationQuotientCompHausColimitMap_comp
    {J : Type} [Category J]
    {D E F : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (υ : E ⟶ F) :
    compactIndexedObservationQuotientCompHausColimitMap (τ ≫ υ) =
      compactIndexedObservationQuotientCompHausColimitMap τ ≫
        compactIndexedObservationQuotientCompHausColimitMap υ := by
  apply colimit.hom_ext
  intro j
  calc
    compactIndexedObservationQuotientCompHausColimitStage D j ≫
        compactIndexedObservationQuotientCompHausColimitMap (τ ≫ υ) =
      (compactIndexedObservationQuotientCompHausMappedNatTrans (τ ≫ υ)).app j ≫
        compactIndexedObservationQuotientCompHausColimitStage F j :=
      colimit.ι_map
        (compactIndexedObservationQuotientCompHausMappedNatTrans (τ ≫ υ)) j
    _ = (compactIndexedObservationQuotientCompHausMappedNatTrans τ).app j ≫
          (compactIndexedObservationQuotientCompHausMappedNatTrans υ).app j ≫
          compactIndexedObservationQuotientCompHausColimitStage F j := by
      simp [compactIndexedObservationQuotientCompHausMappedNatTrans,
        Category.assoc]
    _ = (compactIndexedObservationQuotientCompHausMappedNatTrans τ).app j ≫
          (compactIndexedObservationQuotientCompHausColimitStage E j ≫
            compactIndexedObservationQuotientCompHausColimitMap υ) := by
      rw [compactIndexedObservationQuotientCompHausColimitStage_map]
    _ = (compactIndexedObservationQuotientCompHausMappedNatTrans τ).app j ≫
          compactIndexedObservationQuotientCompHausColimitStage E j ≫
            compactIndexedObservationQuotientCompHausColimitMap υ := by
      simp [Category.assoc]
    _ = (compactIndexedObservationQuotientCompHausColimitStage D j ≫
          compactIndexedObservationQuotientCompHausColimitMap τ) ≫
          compactIndexedObservationQuotientCompHausColimitMap υ := by
      simpa only [Category.assoc] using
        congrArg
          (fun f => f ≫
            compactIndexedObservationQuotientCompHausColimitMap υ)
          (compactIndexedObservationQuotientCompHausColimitStage_map τ j).symm
    _ = compactIndexedObservationQuotientCompHausColimitStage D j ≫
          compactIndexedObservationQuotientCompHausColimitMap τ ≫
            compactIndexedObservationQuotientCompHausColimitMap υ := by
      simp [Category.assoc]

theorem compactIndexedObservationQuotientCompHausColimit_hom_ext
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι)
    {X : CompHaus}
    (f g : compactIndexedObservationQuotientCompHausColimit D ⟶ X)
    (h : ∀ j,
      compactIndexedObservationQuotientCompHausColimitStage D j ≫ f =
        compactIndexedObservationQuotientCompHausColimitStage D j ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro j
  exact h j

noncomputable def compactIndexedObservationQuotientRangeCompHausColimitIso
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationQuotientCompHausColimit D ≅
      colimit (compactIndexedObservationRangeDiagram D) :=
  HasColimit.isoOfNatIso
    (compactIndexedObservationQuotientRangeNaturalIso D)

theorem compactIndexedObservationQuotientRangeCompHausColimitIso_stage
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) (j : J) :
    compactIndexedObservationQuotientCompHausColimitStage D j ≫
        (compactIndexedObservationQuotientRangeCompHausColimitIso D).hom =
      (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
        colimit.ι (compactIndexedObservationRangeDiagram D) j :=
  HasColimit.isoOfNatIso_ι_hom
    (compactIndexedObservationQuotientRangeNaturalIso D) j

noncomputable def compactIndexedObservationRangeCompHausMappedNatTrans
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationRangeDiagram D ⟶
      compactIndexedObservationRangeDiagram E where
  app j := compactSymbolicLatentObservationRangeCompHausFunctor.map
    (τ.app j)
  naturality := by
    intro j k f
    change
      compactSymbolicLatentObservationRangeCompHausFunctor.map (D.map f) ≫
          compactSymbolicLatentObservationRangeCompHausFunctor.map
            (τ.app k) =
        compactSymbolicLatentObservationRangeCompHausFunctor.map
            (τ.app j) ≫
          compactSymbolicLatentObservationRangeCompHausFunctor.map
            (E.map f)
    rw [← compactSymbolicLatentObservationRangeCompHausFunctor.map_comp,
      ← compactSymbolicLatentObservationRangeCompHausFunctor.map_comp,
      τ.naturality]

noncomputable def compactIndexedObservationRangeCompHausColimitMap
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    colimit (compactIndexedObservationRangeDiagram D) ⟶
      colimit (compactIndexedObservationRangeDiagram E) :=
  colim.map (compactIndexedObservationRangeCompHausMappedNatTrans τ)

theorem compactIndexedObservationRangeCompHausColimitStage_map
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (j : J) :
    colimit.ι (compactIndexedObservationRangeDiagram D) j ≫
        compactIndexedObservationRangeCompHausColimitMap τ =
      (compactIndexedObservationRangeCompHausMappedNatTrans τ).app j ≫
        colimit.ι (compactIndexedObservationRangeDiagram E) j :=
  colimit.ι_map (compactIndexedObservationRangeCompHausMappedNatTrans τ) j

theorem compactIndexedObservationRangeCompHausColimitMap_id
    {J : Type} [Category J]
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationRangeCompHausColimitMap (𝟙 D) = 𝟙 _ := by
  apply colimit.hom_ext
  intro j
  change
    colimit.ι (compactIndexedObservationRangeDiagram D) j ≫
        colim.map (compactIndexedObservationRangeCompHausMappedNatTrans (𝟙 D)) =
      colimit.ι (compactIndexedObservationRangeDiagram D) j ≫ 𝟙 _
  rw [colimit.ι_map]
  change
    compactSymbolicLatentObservationRangeCompHausFunctor.map (𝟙 (D.obj j)) ≫
        colimit.ι (compactIndexedObservationRangeDiagram D) j =
      colimit.ι (compactIndexedObservationRangeDiagram D) j
  rw [compactSymbolicLatentObservationRangeCompHausFunctor.map_id,
    Category.id_comp]

theorem compactIndexedObservationRangeCompHausColimitMap_comp
    {J : Type} [Category J]
    {D E F : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (υ : E ⟶ F) :
    compactIndexedObservationRangeCompHausColimitMap (τ ≫ υ) =
      compactIndexedObservationRangeCompHausColimitMap τ ≫
        compactIndexedObservationRangeCompHausColimitMap υ := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι (compactIndexedObservationRangeDiagram D) j ≫
          compactIndexedObservationRangeCompHausColimitMap (τ ≫ υ) =
      (compactIndexedObservationRangeCompHausMappedNatTrans (τ ≫ υ)).app j ≫
        colimit.ι (compactIndexedObservationRangeDiagram F) j :=
      colimit.ι_map
        (compactIndexedObservationRangeCompHausMappedNatTrans (τ ≫ υ)) j
    _ = (compactIndexedObservationRangeCompHausMappedNatTrans τ).app j ≫
          (compactIndexedObservationRangeCompHausMappedNatTrans υ).app j ≫
          colimit.ι (compactIndexedObservationRangeDiagram F) j := by
      simp [compactIndexedObservationRangeCompHausMappedNatTrans,
        Category.assoc]
    _ = (compactIndexedObservationRangeCompHausMappedNatTrans τ).app j ≫
          (colimit.ι (compactIndexedObservationRangeDiagram E) j ≫
            compactIndexedObservationRangeCompHausColimitMap υ) := by
      rw [compactIndexedObservationRangeCompHausColimitStage_map]
    _ = (compactIndexedObservationRangeCompHausMappedNatTrans τ).app j ≫
          colimit.ι (compactIndexedObservationRangeDiagram E) j ≫
            compactIndexedObservationRangeCompHausColimitMap υ := by
      simp [Category.assoc]
    _ = (colimit.ι (compactIndexedObservationRangeDiagram D) j ≫
          compactIndexedObservationRangeCompHausColimitMap τ) ≫
          compactIndexedObservationRangeCompHausColimitMap υ := by
      simpa only [Category.assoc] using
        congrArg
          (fun f => f ≫
            compactIndexedObservationRangeCompHausColimitMap υ)
          (compactIndexedObservationRangeCompHausColimitStage_map τ j).symm
    _ = colimit.ι (compactIndexedObservationRangeDiagram D) j ≫
          compactIndexedObservationRangeCompHausColimitMap τ ≫
            compactIndexedObservationRangeCompHausColimitMap υ := by
      simp [Category.assoc]

theorem compactIndexedObservationQuotientRangeCompHausColimitIso_naturality
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationQuotientCompHausColimitMap τ ≫
        (compactIndexedObservationQuotientRangeCompHausColimitIso E).hom =
      (compactIndexedObservationQuotientRangeCompHausColimitIso D).hom ≫
        compactIndexedObservationRangeCompHausColimitMap τ := by
  apply colimit.hom_ext
  intro j
  calc
    compactIndexedObservationQuotientCompHausColimitStage D j ≫
          compactIndexedObservationQuotientCompHausColimitMap τ ≫
        (compactIndexedObservationQuotientRangeCompHausColimitIso E).hom =
      (compactIndexedObservationQuotientCompHausMappedNatTrans τ).app j ≫
          compactIndexedObservationQuotientCompHausColimitStage E j ≫
        (compactIndexedObservationQuotientRangeCompHausColimitIso E).hom := by
      simpa [Category.assoc] using
        congrArg
          (fun f => f ≫
            (compactIndexedObservationQuotientRangeCompHausColimitIso E).hom)
          (compactIndexedObservationQuotientCompHausColimitStage_map τ j)
    _ = (compactIndexedObservationQuotientCompHausMappedNatTrans τ).app j ≫
          (compactIndexedObservationQuotientRangeNaturalIso E).hom.app j ≫
          colimit.ι (compactIndexedObservationRangeDiagram E) j := by
      rw [compactIndexedObservationQuotientRangeCompHausColimitIso_stage]
    _ = (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
          (compactIndexedObservationRangeCompHausMappedNatTrans τ).app j ≫
          colimit.ι (compactIndexedObservationRangeDiagram E) j := by
      change
        compactSymbolicLatentObservationQuotientCompHausFunctor.map (τ.app j) ≫
            (compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
              (ι := ι)).hom.app (E.obj j) ≫
          colimit.ι (compactIndexedObservationRangeDiagram E) j =
        (compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
            (ι := ι)).hom.app (D.obj j) ≫
            compactSymbolicLatentObservationRangeCompHausFunctor.map (τ.app j) ≫
          colimit.ι (compactIndexedObservationRangeDiagram E) j
      simpa [Category.assoc] using
        congrArg
          (fun f => f ≫ colimit.ι (compactIndexedObservationRangeDiagram E) j)
          ((compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
            (ι := ι)).hom.naturality (τ.app j))
    _ = (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
          colimit.ι (compactIndexedObservationRangeDiagram D) j ≫
          compactIndexedObservationRangeCompHausColimitMap τ := by
      simpa [Category.assoc] using
        congrArg
          (fun f => (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫ f)
          (compactIndexedObservationRangeCompHausColimitStage_map τ j).symm
    _ = compactIndexedObservationQuotientCompHausColimitStage D j ≫
          (compactIndexedObservationQuotientRangeCompHausColimitIso D).hom ≫
          compactIndexedObservationRangeCompHausColimitMap τ := by
      simpa [Category.assoc] using
        congrArg
          (fun f => f ≫ compactIndexedObservationRangeCompHausColimitMap τ)
          (compactIndexedObservationQuotientRangeCompHausColimitIso_stage D j).symm

theorem compactIndexedObservationQuotientRangeCompHausColimitIso_inv_naturality
    {J : Type} [Category J]
    {D E : J ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    (compactIndexedObservationQuotientRangeCompHausColimitIso D).inv ≫
        compactIndexedObservationQuotientCompHausColimitMap τ =
      compactIndexedObservationRangeCompHausColimitMap τ ≫
        (compactIndexedObservationQuotientRangeCompHausColimitIso E).inv := by
  apply (cancel_mono
    (compactIndexedObservationQuotientRangeCompHausColimitIso E).hom).1
  rw [Category.assoc,
    compactIndexedObservationQuotientRangeCompHausColimitIso_naturality τ]
  simp [Category.assoc]

end InfoGeometry.Topology
