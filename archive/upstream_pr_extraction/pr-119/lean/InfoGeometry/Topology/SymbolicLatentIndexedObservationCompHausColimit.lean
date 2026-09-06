import InfoGeometry.Topology.SymbolicLatentIndexedObservationRangeCompHausFunctor

/-!
# Colimits of compact indexed observation ranges

This owner keeps the compact observation-range colimit in `CompHaus`.  It does
not identify that colimit with a colimit of the noncompact ambient coordinate
carrier.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationRangeColimit
    {J : Type} [Category J]
    (D : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)) : CompHaus :=
  colimit (D ⋙ compactIndexedObservationRangeCompHausFunctor)

noncomputable def compactIndexedObservationRangeColimitStage
    {J : Type} [Category J]
    (D : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι))
    (j : J) :
    (compactIndexedObservationRangeCompHausFunctor.obj (D.obj j)) ⟶
      compactIndexedObservationRangeColimit D :=
  colimit.ι (D ⋙ compactIndexedObservationRangeCompHausFunctor) j

noncomputable def compactIndexedObservationRangeMappedNatTrans
    {J : Type} [Category J]
    {D E : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (τ : D ⟶ E) :
    (D ⋙ compactIndexedObservationRangeCompHausFunctor) ⟶
      (E ⋙ compactIndexedObservationRangeCompHausFunctor) where
  app j := compactIndexedObservationRangeCompHausFunctor.map (τ.app j)
  naturality := by
    intro j k f
    change
      compactIndexedObservationRangeCompHausFunctor.map (D.map f) ≫
          compactIndexedObservationRangeCompHausFunctor.map (τ.app k) =
        compactIndexedObservationRangeCompHausFunctor.map (τ.app j) ≫
          compactIndexedObservationRangeCompHausFunctor.map (E.map f)
    rw [← compactIndexedObservationRangeCompHausFunctor.map_comp,
      ← compactIndexedObservationRangeCompHausFunctor.map_comp,
      τ.naturality]

theorem compactIndexedObservationRangeMappedNatTrans_id
    {J : Type} [Category J]
    (D : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)) :
    compactIndexedObservationRangeMappedNatTrans (𝟙 D) = 𝟙 _ := by
  ext j
  simp [compactIndexedObservationRangeMappedNatTrans]

theorem compactIndexedObservationRangeMappedNatTrans_comp
    {J : Type} [Category J]
    {D E F : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (τ : D ⟶ E) (σ : E ⟶ F) :
    compactIndexedObservationRangeMappedNatTrans (τ ≫ σ) =
      compactIndexedObservationRangeMappedNatTrans τ ≫
        compactIndexedObservationRangeMappedNatTrans σ := by
  ext j
  simp [compactIndexedObservationRangeMappedNatTrans]

noncomputable def compactIndexedObservationRangeColimitMap
    {J : Type} [Category J]
    {D E : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (τ : D ⟶ E) :
  compactIndexedObservationRangeColimit D ⟶
      compactIndexedObservationRangeColimit E :=
  colim.map (compactIndexedObservationRangeMappedNatTrans τ)

theorem compactIndexedObservationRangeColimitStage_map
    {J : Type} [Category J]
    {D E : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (τ : D ⟶ E) (j : J) :
    compactIndexedObservationRangeColimitStage D j ≫
        compactIndexedObservationRangeColimitMap τ =
      (compactIndexedObservationRangeMappedNatTrans τ).app j ≫
        compactIndexedObservationRangeColimitStage E j :=
  colimit.ι_map (compactIndexedObservationRangeMappedNatTrans τ) j

@[simp] theorem compactIndexedObservationRangeColimitStage_map_apply
    {J : Type} [Category J]
    {D E : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (τ : D ⟶ E) (j : J)
    (y : compactIndexedObservationRangeCompHausFunctor.obj (D.obj j)) :
    (compactIndexedObservationRangeColimitStage D j ≫
        compactIndexedObservationRangeColimitMap τ) y =
      compactIndexedObservationRangeColimitStage E j
        (compactIndexedObservationRangeCompHausFunctor.map (τ.app j) y) := by
  exact congrArg (fun h => h y)
    (compactIndexedObservationRangeColimitStage_map τ j)

theorem compactIndexedObservationRangeColimit_hom_ext
    {J : Type} [Category J]
    (D : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι))
    {X : CompHaus} (f g : compactIndexedObservationRangeColimit D ⟶ X)
    (h : ∀ j,
      compactIndexedObservationRangeColimitStage D j ≫ f =
        compactIndexedObservationRangeColimitStage D j ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro j
  exact h j

theorem compactIndexedObservationRangeColimitMap_id
    {J : Type} [Category J]
    (D : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)) :
    compactIndexedObservationRangeColimitMap (𝟙 D) = 𝟙 _ := by
  apply compactIndexedObservationRangeColimit_hom_ext D
  intro j
  rw [compactIndexedObservationRangeColimitStage_map]
  simp [compactIndexedObservationRangeMappedNatTrans]

theorem compactIndexedObservationRangeColimitMap_comp
    {J : Type} [Category J]
    {D E F : J ⥤ CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (τ : D ⟶ E) (σ : E ⟶ F) :
    compactIndexedObservationRangeColimitMap (τ ≫ σ) =
      compactIndexedObservationRangeColimitMap τ ≫
        compactIndexedObservationRangeColimitMap σ := by
  apply compactIndexedObservationRangeColimit_hom_ext D
  intro j
  calc
    compactIndexedObservationRangeColimitStage D j ≫
          compactIndexedObservationRangeColimitMap (τ ≫ σ) =
        (compactIndexedObservationRangeMappedNatTrans (τ ≫ σ)).app j ≫
          compactIndexedObservationRangeColimitStage F j :=
      compactIndexedObservationRangeColimitStage_map (τ ≫ σ) j
    _ = compactIndexedObservationRangeCompHausFunctor.map (τ.app j) ≫
          compactIndexedObservationRangeCompHausFunctor.map (σ.app j) ≫
            compactIndexedObservationRangeColimitStage F j := by
      simp [compactIndexedObservationRangeMappedNatTrans,
        Category.assoc]
    _ = compactIndexedObservationRangeCompHausFunctor.map (τ.app j) ≫
          (compactIndexedObservationRangeColimitStage E j ≫
            compactIndexedObservationRangeColimitMap σ) := by
      rw [compactIndexedObservationRangeColimitStage_map σ j]
      simp [compactIndexedObservationRangeMappedNatTrans]
    _ = (compactIndexedObservationRangeColimitStage D j ≫
          compactIndexedObservationRangeColimitMap τ) ≫
            compactIndexedObservationRangeColimitMap σ := by
      rw [compactIndexedObservationRangeColimitStage_map τ j]
      simp [compactIndexedObservationRangeMappedNatTrans, Category.assoc]

end
end InfoGeometry.Topology
