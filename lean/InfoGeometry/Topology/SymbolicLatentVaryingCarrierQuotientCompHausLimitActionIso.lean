import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Invertible actions on indexed varying-carrier inverse limits

The additive law for an indexed family supplies the inverse at time `-t`.
This owner packages the induced quotient and observation-range endomorphisms
as genuine `CompHaus` isomorphisms.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimitActionIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimit D ≅
      compactIndexedObservationQuotientCompHausLimit D :=
  { hom := compactIndexedObservationQuotientCompHausLimitAction D α t
    inv := compactIndexedObservationQuotientCompHausLimitAction D α (-t)
    hom_inv_id := by
      change compactIndexedObservationQuotientCompHausLimitMap (α t) ≫
        compactIndexedObservationQuotientCompHausLimitMap (α (-t)) = 𝟙 _
      rw [← compactIndexedObservationQuotientCompHausLimitMap_comp,
        ← hαadd, add_neg_cancel, hα0,
        compactIndexedObservationQuotientCompHausLimitMap_id]
    inv_hom_id := by
      change compactIndexedObservationQuotientCompHausLimitMap (α (-t)) ≫
        compactIndexedObservationQuotientCompHausLimitMap (α t) = 𝟙 _
      rw [← compactIndexedObservationQuotientCompHausLimitMap_comp,
        ← hαadd, neg_add_cancel, hα0,
        compactIndexedObservationQuotientCompHausLimitMap_id] }

theorem compactIndexedObservationQuotientCompHausLimitActionIso_hom
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    (compactIndexedObservationQuotientCompHausLimitActionIso
      D α hα0 hαadd t).hom =
      compactIndexedObservationQuotientCompHausLimitAction D α t :=
  rfl

theorem compactIndexedObservationQuotientCompHausLimitActionIso_inv
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    (compactIndexedObservationQuotientCompHausLimitActionIso
      D α hα0 hαadd t).inv =
      compactIndexedObservationQuotientCompHausLimitAction D α (-t) :=
  rfl

noncomputable def compactIndexedObservationRangeCompHausLimitActionIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimit D ≅
      compactIndexedObservationRangeCompHausLimit D :=
  { hom := compactIndexedObservationRangeCompHausLimitAction D α t
    inv := compactIndexedObservationRangeCompHausLimitAction D α (-t)
    hom_inv_id := by
      change compactIndexedObservationRangeCompHausLimitMap (α t) ≫
        compactIndexedObservationRangeCompHausLimitMap (α (-t)) = 𝟙 _
      rw [← compactIndexedObservationRangeCompHausLimitMap_comp,
        ← hαadd, add_neg_cancel, hα0,
        compactIndexedObservationRangeCompHausLimitMap_id]
    inv_hom_id := by
      change compactIndexedObservationRangeCompHausLimitMap (α (-t)) ≫
        compactIndexedObservationRangeCompHausLimitMap (α t) = 𝟙 _
      rw [← compactIndexedObservationRangeCompHausLimitMap_comp,
        ← hαadd, neg_add_cancel, hα0,
        compactIndexedObservationRangeCompHausLimitMap_id] }

theorem compactIndexedObservationRangeCompHausLimitActionIso_hom
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    (compactIndexedObservationRangeCompHausLimitActionIso
      D α hα0 hαadd t).hom =
      compactIndexedObservationRangeCompHausLimitAction D α t :=
  rfl

theorem compactIndexedObservationRangeCompHausLimitActionIso_inv
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    (compactIndexedObservationRangeCompHausLimitActionIso
      D α hα0 hαadd t).inv =
      compactIndexedObservationRangeCompHausLimitAction D α (-t) :=
  rfl

theorem compactIndexedObservationQuotientRangeCompHausLimitIso_actionIso_naturality
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    (compactIndexedObservationQuotientCompHausLimitActionIso
      D α hα0 hαadd t).hom ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom =
      (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom ≫
        (compactIndexedObservationRangeCompHausLimitActionIso
          D α hα0 hαadd t).hom := by
  exact compactIndexedObservationQuotientRangeCompHausLimitIso_action_naturality
    D α t

end InfoGeometry.Topology
