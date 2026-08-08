import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausIndexed
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Projective limits of compact symbolic-latent quotient diagrams

For a contravariant diagram of compact symbolic-latent systems, the quotient
and observation-range diagrams sorry genuine `CompHaus` limits.  This owner
uses Mathlib's native `limit`, `lim.map`, and `HasLimit.isoOfNatIso`; it does
not introduce a separate compatible-family or state-space surrogate.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) : CompHaus :=
  limit (compactIndexedObservationQuotientDiagram D)

noncomputable def compactIndexedObservationQuotientCompHausLimitProjection
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) (j : Jᵒᵖ) :
    compactIndexedObservationQuotientCompHausLimit D ⟶
      (compactIndexedObservationQuotientDiagram D).obj j :=
  limit.π (compactIndexedObservationQuotientDiagram D) j

noncomputable def compactIndexedObservationQuotientCompHausLimitMappedNatTrans
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
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

noncomputable def compactIndexedObservationQuotientCompHausLimitMap
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationQuotientCompHausLimit D ⟶
      compactIndexedObservationQuotientCompHausLimit E :=
  lim.map (compactIndexedObservationQuotientCompHausLimitMappedNatTrans τ)

theorem compactIndexedObservationQuotientCompHausLimitMap_projection
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (j : Jᵒᵖ) :
    compactIndexedObservationQuotientCompHausLimitMap τ ≫
        compactIndexedObservationQuotientCompHausLimitProjection E j =
      compactIndexedObservationQuotientCompHausLimitProjection D j ≫
        (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
          (D := D) (E := E) τ).app j := by
  change IsLimit.map
      (limit.cone (compactIndexedObservationQuotientDiagram D))
      (limit.isLimit (compactIndexedObservationQuotientDiagram E))
      (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
          (D := D) (E := E) τ) ≫
        (limit.cone (compactIndexedObservationQuotientDiagram E)).π.app j =
    (limit.cone (compactIndexedObservationQuotientDiagram D)).π.app j ≫
      (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
          (D := D) (E := E) τ).app j
  exact IsLimit.map_π
    (limit.cone (compactIndexedObservationQuotientDiagram D))
    (limit.isLimit (compactIndexedObservationQuotientDiagram E))
    (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
        (D := D) (E := E) τ) j

theorem compactIndexedObservationQuotientCompHausLimit_hom_ext
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    {X : CompHaus}
    (f g : X ⟶ compactIndexedObservationQuotientCompHausLimit D)
    (h : ∀ j,
      f ≫ compactIndexedObservationQuotientCompHausLimitProjection D j =
        g ≫ compactIndexedObservationQuotientCompHausLimitProjection D j) :
    f = g := by
  apply limit.hom_ext
  intro j
  exact h j

theorem compactIndexedObservationQuotientCompHausLimitMap_id
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationQuotientCompHausLimitMap (𝟙 D) = 𝟙 _ := by
  apply limit.hom_ext
  intro j
  change
    compactIndexedObservationQuotientCompHausLimitMap (𝟙 D) ≫
        compactIndexedObservationQuotientCompHausLimitProjection D j =
    𝟙 _ ≫ compactIndexedObservationQuotientCompHausLimitProjection D j
  rw [compactIndexedObservationQuotientCompHausLimitMap_projection]
  change
    compactIndexedObservationQuotientCompHausLimitProjection D j ≫
      compactSymbolicLatentObservationQuotientCompHausFunctor.map
        (𝟙 (D.obj j)) =
    𝟙 _ ≫ compactIndexedObservationQuotientCompHausLimitProjection D j
  rw [compactSymbolicLatentObservationQuotientCompHausFunctor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem compactIndexedObservationQuotientCompHausLimitMap_comp
    {J : Type} [Category J]
    {D E F : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (υ : E ⟶ F) :
    compactIndexedObservationQuotientCompHausLimitMap (τ ≫ υ) =
      compactIndexedObservationQuotientCompHausLimitMap τ ≫
        compactIndexedObservationQuotientCompHausLimitMap υ := by
  apply limit.hom_ext
  intro j
  calc
    compactIndexedObservationQuotientCompHausLimitMap (τ ≫ υ) ≫
          compactIndexedObservationQuotientCompHausLimitProjection F j =
        compactIndexedObservationQuotientCompHausLimitProjection D j ≫
          (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
            (D := D) (E := F) (τ ≫ υ)).app j :=
      compactIndexedObservationQuotientCompHausLimitMap_projection (τ ≫ υ) j
    _ = compactIndexedObservationQuotientCompHausLimitProjection D j ≫
          (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j ≫
          (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
            (D := E) (E := F) υ).app j := by
      simp [compactIndexedObservationQuotientCompHausLimitMappedNatTrans]
    _ = (compactIndexedObservationQuotientCompHausLimitMap τ ≫
          compactIndexedObservationQuotientCompHausLimitProjection E j) ≫
          (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
            (D := E) (E := F) υ).app j := by
      rw [compactIndexedObservationQuotientCompHausLimitMap_projection τ j]
      exact (Category.assoc _ _ _).symm
    _ = compactIndexedObservationQuotientCompHausLimitMap τ ≫
          (compactIndexedObservationQuotientCompHausLimitProjection E j ≫
            (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
              (D := E) (E := F) υ).app j) := by
      exact Category.assoc _ _ _
    _ = compactIndexedObservationQuotientCompHausLimitMap τ ≫
          (compactIndexedObservationQuotientCompHausLimitMap υ ≫
            compactIndexedObservationQuotientCompHausLimitProjection F j) := by
      rw [compactIndexedObservationQuotientCompHausLimitMap_projection υ j]
    _ = (compactIndexedObservationQuotientCompHausLimitMap τ ≫
          compactIndexedObservationQuotientCompHausLimitMap υ) ≫
          compactIndexedObservationQuotientCompHausLimitProjection F j := by
      simp [Category.assoc]

noncomputable def compactIndexedObservationRangeCompHausLimit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) : CompHaus :=
  limit (compactIndexedObservationRangeDiagram D)

noncomputable def compactIndexedObservationQuotientRangeCompHausLimitIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationQuotientCompHausLimit D ≅
      compactIndexedObservationRangeCompHausLimit D :=
  HasLimit.isoOfNatIso (compactIndexedObservationQuotientRangeNaturalIso D)

theorem compactIndexedObservationQuotientRangeCompHausLimitIso_projection
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) (j : Jᵒᵖ) :
    (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
        limit.π (compactIndexedObservationRangeDiagram D) j =
      limit.π (compactIndexedObservationQuotientDiagram D) j ≫
        (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j :=
  HasLimit.isoOfNatIso_hom_π
    (compactIndexedObservationQuotientRangeNaturalIso D) j

noncomputable def compactIndexedObservationRangeCompHausLimitMappedNatTrans
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
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

noncomputable def compactIndexedObservationRangeCompHausLimitMap
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationRangeCompHausLimit D ⟶
      compactIndexedObservationRangeCompHausLimit E :=
  lim.map (compactIndexedObservationRangeCompHausLimitMappedNatTrans τ)

theorem compactIndexedObservationRangeCompHausLimitMap_projection
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (j : Jᵒᵖ) :
    compactIndexedObservationRangeCompHausLimitMap τ ≫
        limit.π (compactIndexedObservationRangeDiagram E) j =
      limit.π (compactIndexedObservationRangeDiagram D) j ≫
        (compactIndexedObservationRangeCompHausLimitMappedNatTrans
          (D := D) (E := E) τ).app j := by
  exact IsLimit.map_π
    (limit.cone (compactIndexedObservationRangeDiagram D))
    (limit.isLimit (compactIndexedObservationRangeDiagram E))
    (compactIndexedObservationRangeCompHausLimitMappedNatTrans τ) j

theorem compactIndexedObservationRangeCompHausLimitMap_id
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationRangeCompHausLimitMap (𝟙 D) = 𝟙 _ := by
  apply limit.hom_ext
  intro j
  change
    compactIndexedObservationRangeCompHausLimitMap (𝟙 D) ≫
        limit.π (compactIndexedObservationRangeDiagram D) j =
    𝟙 _ ≫ limit.π (compactIndexedObservationRangeDiagram D) j
  rw [compactIndexedObservationRangeCompHausLimitMap_projection]
  change
    limit.π (compactIndexedObservationRangeDiagram D) j ≫
      compactSymbolicLatentObservationRangeCompHausFunctor.map
        (𝟙 (D.obj j)) =
    𝟙 _ ≫ limit.π (compactIndexedObservationRangeDiagram D) j
  rw [compactSymbolicLatentObservationRangeCompHausFunctor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem compactIndexedObservationRangeCompHausLimitMap_comp
    {J : Type} [Category J]
    {D E F : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) (υ : E ⟶ F) :
    compactIndexedObservationRangeCompHausLimitMap (τ ≫ υ) =
      compactIndexedObservationRangeCompHausLimitMap τ ≫
        compactIndexedObservationRangeCompHausLimitMap υ := by
  apply limit.hom_ext
  intro j
  calc
    compactIndexedObservationRangeCompHausLimitMap (τ ≫ υ) ≫
          limit.π (compactIndexedObservationRangeDiagram F) j =
        limit.π (compactIndexedObservationRangeDiagram D) j ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := D) (E := F) (τ ≫ υ)).app j :=
      compactIndexedObservationRangeCompHausLimitMap_projection (τ ≫ υ) j
    _ = limit.π (compactIndexedObservationRangeDiagram D) j ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := E) (E := F) υ).app j := by
      simp [compactIndexedObservationRangeCompHausLimitMappedNatTrans]
    _ = (compactIndexedObservationRangeCompHausLimitMap τ ≫
          limit.π (compactIndexedObservationRangeDiagram E) j) ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := E) (E := F) υ).app j := by
      rw [compactIndexedObservationRangeCompHausLimitMap_projection τ j]
      exact (Category.assoc _ _ _).symm
    _ = compactIndexedObservationRangeCompHausLimitMap τ ≫
          (limit.π (compactIndexedObservationRangeDiagram E) j ≫
            (compactIndexedObservationRangeCompHausLimitMappedNatTrans
              (D := E) (E := F) υ).app j) := by
      exact Category.assoc _ _ _
    _ = compactIndexedObservationRangeCompHausLimitMap τ ≫
          (compactIndexedObservationRangeCompHausLimitMap υ ≫
            limit.π (compactIndexedObservationRangeDiagram F) j) := by
      rw [compactIndexedObservationRangeCompHausLimitMap_projection υ j]
    _ = (compactIndexedObservationRangeCompHausLimitMap τ ≫
          compactIndexedObservationRangeCompHausLimitMap υ) ≫
          limit.π (compactIndexedObservationRangeDiagram F) j := by
      simp [Category.assoc]

theorem compactIndexedObservationQuotientRangeCompHausLimitIso_naturality
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    compactIndexedObservationQuotientCompHausLimitMap τ ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso E).hom =
      (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
        compactIndexedObservationRangeCompHausLimitMap τ := by
  apply limit.hom_ext
  intro j
  calc
    compactIndexedObservationQuotientCompHausLimitMap τ ≫
          (compactIndexedObservationQuotientRangeCompHausLimitIso E).hom ≫
        limit.π (compactIndexedObservationRangeDiagram E) j =
      compactIndexedObservationQuotientCompHausLimitMap τ ≫
          limit.π (compactIndexedObservationQuotientDiagram E) j ≫
        (compactIndexedObservationQuotientRangeNaturalIso E).hom.app j := by
      rw [compactIndexedObservationQuotientRangeCompHausLimitIso_projection]
    _ = compactIndexedObservationQuotientCompHausLimitProjection D j ≫
          (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j ≫
          (compactIndexedObservationQuotientRangeNaturalIso E).hom.app j := by
      change
        compactIndexedObservationQuotientCompHausLimitMap τ ≫
            compactIndexedObservationQuotientCompHausLimitProjection E j ≫
          (compactIndexedObservationQuotientRangeNaturalIso E).hom.app j =
        compactIndexedObservationQuotientCompHausLimitProjection D j ≫
            (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
              (D := D) (E := E) τ).app j ≫
          (compactIndexedObservationQuotientRangeNaturalIso E).hom.app j
      simpa only [Category.assoc] using
        congrArg
          (fun f => f ≫
            (compactIndexedObservationQuotientRangeNaturalIso E).hom.app j)
          (compactIndexedObservationQuotientCompHausLimitMap_projection τ j)
    _ = compactIndexedObservationQuotientCompHausLimitProjection D j ≫
          (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j := by
      change
        compactIndexedObservationQuotientCompHausLimitProjection D j ≫
            (compactSymbolicLatentObservationQuotientCompHausFunctor.map
              (τ.app j) ≫
              (compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
                (ι := ι)).hom.app (E.obj j)) =
          compactIndexedObservationQuotientCompHausLimitProjection D j ≫
            ((compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
              (ι := ι)).hom.app (D.obj j) ≫
              compactSymbolicLatentObservationRangeCompHausFunctor.map
                (τ.app j))
      simpa only [Category.assoc] using
        congrArg
          (fun f => compactIndexedObservationQuotientCompHausLimitProjection D j ≫ f)
          ((compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
            (ι := ι)).hom.naturality (τ.app j))
    _ = (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
          limit.π (compactIndexedObservationRangeDiagram D) j ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j := by
      change
        limit.π (compactIndexedObservationQuotientDiagram D) j ≫
            (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j =
        ((compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
            limit.π (compactIndexedObservationRangeDiagram D) j) ≫
          (compactIndexedObservationRangeCompHausLimitMappedNatTrans
            (D := D) (E := E) τ).app j
      rw [compactIndexedObservationQuotientRangeCompHausLimitIso_projection]
      exact (Category.assoc _ _ _).symm
    _ = (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
          compactIndexedObservationRangeCompHausLimitMap τ ≫
          limit.π (compactIndexedObservationRangeDiagram E) j := by
      rw [compactIndexedObservationRangeCompHausLimitMap_projection τ j]

theorem compactIndexedObservationQuotientRangeCompHausLimitIso_inv_naturality
    {J : Type} [Category J]
    {D E : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι}
    (τ : D ⟶ E) :
    (compactIndexedObservationQuotientRangeCompHausLimitIso D).inv ≫
        compactIndexedObservationQuotientCompHausLimitMap τ =
      compactIndexedObservationRangeCompHausLimitMap τ ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso E).inv := by
  apply (cancel_mono
    (compactIndexedObservationQuotientRangeCompHausLimitIso E).hom).1
  rw [Category.assoc,
    compactIndexedObservationQuotientRangeCompHausLimitIso_naturality τ]
  simp [Category.assoc]

end InfoGeometry.Topology
