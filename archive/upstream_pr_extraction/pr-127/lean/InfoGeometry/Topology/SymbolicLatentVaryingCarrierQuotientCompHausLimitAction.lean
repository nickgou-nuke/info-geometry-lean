import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimit

/-!
# Actions on indexed varying-carrier inverse limits

An indexed family of endomorphisms of a varying-carrier symbolic-latent
system induces an endomorphism of the quotient and observation-range limits.
The action laws are assumptions on the indexed system morphisms and are
transported by the native `lim.map` construction.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimitAction
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimit D ⟶
      compactIndexedObservationQuotientCompHausLimit D :=
  compactIndexedObservationQuotientCompHausLimitMap (α t)

theorem compactIndexedObservationQuotientCompHausLimitAction_projection
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) (j : Jᵒᵖ) :
    compactIndexedObservationQuotientCompHausLimitAction D α t ≫
        compactIndexedObservationQuotientCompHausLimitProjection D j =
      compactIndexedObservationQuotientCompHausLimitProjection D j ≫
        (compactIndexedObservationQuotientCompHausLimitMappedNatTrans
          (D := D) (E := D) (α t)).app j := by
  exact compactIndexedObservationQuotientCompHausLimitMap_projection
    (α t) j

theorem compactIndexedObservationQuotientCompHausLimitAction_zero
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D) :
    compactIndexedObservationQuotientCompHausLimitAction D α 0 = 𝟙 _ := by
  rw [compactIndexedObservationQuotientCompHausLimitAction, hα0,
    compactIndexedObservationQuotientCompHausLimitMap_id]

theorem compactIndexedObservationQuotientCompHausLimitAction_add
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitAction D α (s + t) =
    compactIndexedObservationQuotientCompHausLimitAction D α s ≫
        compactIndexedObservationQuotientCompHausLimitAction D α t := by
  change compactIndexedObservationQuotientCompHausLimitMap (α (s + t)) =
    compactIndexedObservationQuotientCompHausLimitMap (α s) ≫
      compactIndexedObservationQuotientCompHausLimitMap (α t)
  rw [hαadd, compactIndexedObservationQuotientCompHausLimitMap_comp]

noncomputable def compactIndexedObservationRangeCompHausLimitAction
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    compactIndexedObservationRangeCompHausLimit D ⟶
      compactIndexedObservationRangeCompHausLimit D :=
  compactIndexedObservationRangeCompHausLimitMap (α t)

theorem compactIndexedObservationRangeCompHausLimitAction_projection
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) (j : Jᵒᵖ) :
    compactIndexedObservationRangeCompHausLimitAction D α t ≫
        limit.π (compactIndexedObservationRangeDiagram D) j =
      limit.π (compactIndexedObservationRangeDiagram D) j ≫
        (compactIndexedObservationRangeCompHausLimitMappedNatTrans
          (D := D) (E := D) (α t)).app j := by
  exact compactIndexedObservationRangeCompHausLimitMap_projection
    (α t) j

theorem compactIndexedObservationRangeCompHausLimitAction_zero
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D) :
    compactIndexedObservationRangeCompHausLimitAction D α 0 = 𝟙 _ := by
  rw [compactIndexedObservationRangeCompHausLimitAction, hα0,
    compactIndexedObservationRangeCompHausLimitMap_id]

theorem compactIndexedObservationRangeCompHausLimitAction_add
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s t : ℝ) :
    compactIndexedObservationRangeCompHausLimitAction D α (s + t) =
    compactIndexedObservationRangeCompHausLimitAction D α s ≫
        compactIndexedObservationRangeCompHausLimitAction D α t := by
  change compactIndexedObservationRangeCompHausLimitMap (α (s + t)) =
    compactIndexedObservationRangeCompHausLimitMap (α s) ≫
      compactIndexedObservationRangeCompHausLimitMap (α t)
  rw [hαadd, compactIndexedObservationRangeCompHausLimitMap_comp]

theorem compactIndexedObservationQuotientRangeCompHausLimitIso_action_naturality
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitAction D α t ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom =
      (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
        compactIndexedObservationRangeCompHausLimitAction D α t :=
  compactIndexedObservationQuotientRangeCompHausLimitIso_naturality
    (α t)

end InfoGeometry.Topology
