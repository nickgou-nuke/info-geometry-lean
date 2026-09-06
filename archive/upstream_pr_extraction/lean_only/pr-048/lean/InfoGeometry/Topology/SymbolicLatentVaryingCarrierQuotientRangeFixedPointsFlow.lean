import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointsCompHaus
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeJointContinuity

/-!
# Restricted flows on fixed-point carriers

The ambient action preserves the fixed-point locus of a time slice.  This
owner turns that invariance into subtype-valued actions, proves their joint
continuity from the ambient joint-continuity theorem, and packages each time
slice as a genuine `CompHaus` morphism.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationQuotientCompHausLimitFixedPointAction
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    ℝ × compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t →
      compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t :=
  fun p =>
    ⟨compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2.1,
      compactIndexedObservationQuotientCompHausLimit_fixedPointSet_invariant
        D α hαadd t p.1 p.2.1 p.2.2⟩

@[simp] theorem compactIndexedObservationQuotientCompHausLimitFixedPointAction_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ)
    (p : ℝ × compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationQuotientCompHausLimitFixedPointAction
        D α hαadd t p =
      ⟨compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2.1,
        compactIndexedObservationQuotientCompHausLimit_fixedPointSet_invariant
          D α hαadd t p.1 p.2.1 p.2.2⟩ :=
  rfl

set_option maxHeartbeats 1000000 in
theorem continuous_compactIndexedObservationQuotientCompHausLimitFixedPointAction
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t : ℝ) :
    Continuous (compactIndexedObservationQuotientCompHausLimitFixedPointAction
      D α hαadd t) := by
  apply Continuous.subtype_mk
  have hinput : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t =>
        (p.1, p.2.1)) := by
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  simpa only [Function.comp_apply] using hjoint.comp hinput

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus D α t ⟶
      compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus D α t := by
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet D α t)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) ⟶
    CompHaus.of (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t)
  exact ⟨TopCat.ofHom
    { toFun := fun x =>
        compactIndexedObservationQuotientCompHausLimitFixedPointAction
          D α hαadd t (s, x)
      continuous_toFun := by
        exact (continuous_compactIndexedObservationQuotientCompHausLimitFixedPointAction
          D α hαadd hjoint t).comp
          (continuous_const.prodMk continuous_id) }⟩

theorem compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t s : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    (compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s x).1 =
      compactIndexedObservationQuotientCompHausLimitAction D α s x.1 :=
  rfl

def compactIndexedObservationRangeCompHausLimitFixedPointAction
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    ℝ × compactIndexedObservationRangeCompHausLimitFixedPointSet D α t →
      compactIndexedObservationRangeCompHausLimitFixedPointSet D α t :=
  fun p =>
    ⟨compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2.1,
      compactIndexedObservationRangeCompHausLimit_fixedPointSet_invariant
        D α hαadd t p.1 p.2.1 p.2.2⟩

set_option maxHeartbeats 1000000 in
theorem continuous_compactIndexedObservationRangeCompHausLimitFixedPointAction
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t : ℝ) :
    Continuous (compactIndexedObservationRangeCompHausLimitFixedPointAction
      D α hαadd t) := by
  apply Continuous.subtype_mk
  have hinput : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimitFixedPointSet D α t =>
        (p.1, p.2.1)) := by
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  simpa only [Function.comp_apply] using hjoint.comp hinput

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    compactIndexedObservationRangeCompHausLimitFixedPointCompHaus D α t ⟶
      compactIndexedObservationRangeCompHausLimitFixedPointCompHaus D α t := by
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet D α t)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) ⟶
    CompHaus.of (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t)
  exact ⟨TopCat.ofHom
    { toFun := fun x =>
        compactIndexedObservationRangeCompHausLimitFixedPointAction
          D α hαadd t (s, x)
      continuous_toFun := by
        exact (continuous_compactIndexedObservationRangeCompHausLimitFixedPointAction
          D α hαadd hjoint t).comp
          (continuous_const.prodMk continuous_id) }⟩

theorem compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t s : ℝ)
    (x : compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :
    (compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s x).1 =
      compactIndexedObservationRangeCompHausLimitAction D α s x.1 :=
  rfl

theorem compactIndexedObservationQuotientCompHausLimitFixedPointAction_zero
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationQuotientCompHausLimitFixedPointAction
        D α hαadd t (0, x) = x := by
  apply Subtype.ext
  have h := congrArg (fun f => f x.1)
    (compactIndexedObservationQuotientCompHausLimitAction_zero D α hα0)
  exact h

theorem compactIndexedObservationQuotientCompHausLimitFixedPointAction_add
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t s r : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationQuotientCompHausLimitFixedPointAction
        D α hαadd t (s,
          compactIndexedObservationQuotientCompHausLimitFixedPointAction
            D α hαadd t (r, x)) =
      compactIndexedObservationQuotientCompHausLimitFixedPointAction
        D α hαadd t (s + r, x) := by
  apply Subtype.ext
  have h := congrArg (fun f => f x.1)
    (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd r s)
  simpa [add_comm] using h.symm

theorem compactIndexedObservationRangeCompHausLimitFixedPointAction_zero
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ)
    (x : compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t (0, x) = x := by
  apply Subtype.ext
  have h := congrArg (fun f => f x.1)
    (compactIndexedObservationRangeCompHausLimitAction_zero D α hα0)
  exact h

theorem compactIndexedObservationRangeCompHausLimitFixedPointAction_add
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t s r : ℝ)
    (x : compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t (s,
          compactIndexedObservationRangeCompHausLimitFixedPointAction
            D α hαadd t (r, x)) =
      compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t (s + r, x) := by
  apply Subtype.ext
  have h := congrArg (fun f => f x.1)
    (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd r s)
  simpa [add_comm] using h.symm

theorem compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_zero
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
      D α hαadd hjoint t 0 = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro x
  change compactIndexedObservationQuotientCompHausLimitFixedPointAction
      D α hαadd t (0, x) = x
  exact compactIndexedObservationQuotientCompHausLimitFixedPointAction_zero
    D α hα0 hαadd t x

theorem compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_comp
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t r s : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t r ≫
      compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s =
      compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t (r + s) := by
  apply ConcreteCategory.hom_ext
  intro x
  change
    compactIndexedObservationQuotientCompHausLimitFixedPointAction
        D α hαadd t
        (s,
          compactIndexedObservationQuotientCompHausLimitFixedPointAction
            D α hαadd t (r, x)) =
      compactIndexedObservationQuotientCompHausLimitFixedPointAction
        D α hαadd t (r + s, x)
  simpa [add_comm] using
    compactIndexedObservationQuotientCompHausLimitFixedPointAction_add
      D α hαadd t s r x

theorem compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_zero
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
      D α hαadd hjoint t 0 = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro x
  change compactIndexedObservationRangeCompHausLimitFixedPointAction
      D α hαadd t (0, x) = x
  exact compactIndexedObservationRangeCompHausLimitFixedPointAction_zero
    D α hα0 hαadd t x

theorem compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_comp
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t r s : ℝ) :
    compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t r ≫
      compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s =
      compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t (r + s) := by
  apply ConcreteCategory.hom_ext
  intro x
  change
    compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t
        (s,
          compactIndexedObservationRangeCompHausLimitFixedPointAction
            D α hαadd t (r, x)) =
      compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t (r + s, x)
  simpa [add_comm] using
    compactIndexedObservationRangeCompHausLimitFixedPointAction_add
      D α hαadd t s r x

theorem compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_comp_neg
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s ≫
      compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t (-s) =
      𝟙 _ := by
  rw [compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_comp]
  rw [add_neg_cancel]
  exact compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_zero
    D α hα0 hαadd hjoint t

theorem compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_comp_neg
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s ≫
      compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t (-s) =
      𝟙 _ := by
  rw [compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_comp]
  rw [add_neg_cancel]
  exact compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_zero
    D α hα0 hαadd hjoint t

theorem compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_isIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    IsIso
      (compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s) := by
  refine IsIso.mk ⟨
    compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
      D α hαadd hjoint t (-s), ?_, ?_⟩
  · exact compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_comp_neg
      D α hα0 hαadd hjoint t s
  · simpa using
      compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom_comp_neg
        D α hα0 hαadd hjoint t (-s)

theorem compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_isIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    IsIso
      (compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
        D α hαadd hjoint t s) := by
  refine IsIso.mk ⟨
    compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
      D α hαadd hjoint t (-s), ?_, ?_⟩
  · exact compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_comp_neg
      D α hα0 hαadd hjoint t s
  · simpa using
      compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom_comp_neg
        D α hα0 hαadd hjoint t (-s)

end InfoGeometry.Topology
