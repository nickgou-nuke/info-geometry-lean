import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointGraphCompHausNaturality
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Fibers of compact fixed-point graphs

For a time `t` in a bounded interval, the fiber of the fixed-point graph over
`t` is homeomorphic to the fixed-point set of the time slice `t.1`.  No
uniqueness of fixed points is assumed.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) : Set
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
  {p | p.1.1.1 = t}

def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) : Set
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
  {p | p.1.1.1 = t}

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isClosed_fiber
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    IsClosed
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) := by
  apply isClosed_eq
  · simpa only [Function.comp_apply] using
    (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val) :
      Continuous (fun p :
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn
          D α a b => (p.1.1.1 : ℝ)))
  · exact continuous_const

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isClosed_fiber
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    IsClosed
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) := by
  apply isClosed_eq
  · simpa only [Function.comp_apply] using
    (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val) :
      Continuous (fun p :
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn
          D α a b => (p.1.1.1 : ℝ)))
  · exact continuous_const

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isCompact_fiber
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    IsCompact
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isClosed_fiber
      D α a b t)
    (Set.subset_univ _)

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isCompact_fiber
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    IsCompact
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isClosed_fiber
      D α a b t)
    (Set.subset_univ _)

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
      D α a b t ≃ₜ
    compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t.1 := by
  refine
    { toFun := fun p =>
        ⟨p.1.1.2, ?_⟩
      invFun := fun x =>
        ⟨⟨(t, x.1), x.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change compactIndexedObservationQuotientCompHausLimitAction D α t.1
      p.1.1.2 = p.1.1.2
    have hp := p.2
    unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber at hp
    change (p.1.1.1 : ℝ) = (t : ℝ) at hp
    rw [← hp]
    exact p.1.2
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change t = p.1.1.1
      have hp := p.2
      unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber at hp
      change (p.1.1.1 : ℝ) = (t : ℝ) at hp
      exact Subtype.ext hp.symm
    · rfl
  · intro x
    apply Subtype.ext
    rfl
  · have hcarrier : Continuous (fun p :
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
          D α a b t => p.1.1.2) := by
      exact continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val)
    exact hcarrier.subtype_mk _
  · exact
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
      D α a b t ≃ₜ
    compactIndexedObservationRangeCompHausLimitFixedPointSet D α t.1 := by
  refine
    { toFun := fun p =>
        ⟨p.1.1.2, ?_⟩
      invFun := fun x =>
        ⟨⟨(t, x.1), x.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change compactIndexedObservationRangeCompHausLimitAction D α t.1
      p.1.1.2 = p.1.1.2
    have hp := p.2
    unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber at hp
    change (p.1.1.1 : ℝ) = (t : ℝ) at hp
    rw [← hp]
    exact p.1.2
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change t = p.1.1.1
      have hp := p.2
      unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber at hp
      change (p.1.1.1 : ℝ) = (t : ℝ) at hp
      exact Subtype.ext hp.symm
    · rfl
  · intro p
    apply Subtype.ext
    rfl
  · have hcarrier : Continuous (fun p :
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
          D α a b t => p.1.1.2) := by
      exact continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val)
    exact hcarrier.subtype_mk _
  · exact
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _

@[simp] theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberHomeomorph_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (p : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
      D α a b t) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberHomeomorph
      D α a b t p = ⟨p.1.1.2, by
        change compactIndexedObservationQuotientCompHausLimitAction D α t.1
          p.1.1.2 = p.1.1.2
        have hp := p.2
        unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber at hp
        change (p.1.1.1 : ℝ) = (t : ℝ) at hp
        rw [← hp]
        exact p.1.2⟩ := rfl

@[simp] theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberHomeomorph_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (p : compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
      D α a b t) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberHomeomorph
      D α a b t p = ⟨p.1.1.2, by
        change compactIndexedObservationRangeCompHausLimitAction D α t.1
          p.1.1.2 = p.1.1.2
        have hp := p.2
        unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber at hp
        change (p.1.1.1 : ℝ) = (t : ℝ) at hp
        rw [← hp]
        exact p.1.2⟩ := rfl

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) : CompHaus := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isCompact_fiber
        D α a b t hjoint)
  exact CompHaus.of
    (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
      D α a b t)

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) : CompHaus := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isCompact_fiber
        D α a b t hjoint)
  exact CompHaus.of
    (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
      D α a b t)

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHausIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHaus
      D α a b t hjoint ≅
    compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus D α t.1 := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isCompact_fiber
        D α a b t hjoint)
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t.1) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet D α t.1)
  let e := compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberHomeomorph
    D α a b t
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) ≅
    CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t.1)
  exact
    { hom := ⟨TopCat.ofHom { toFun := e, continuous_toFun := e.continuous }⟩
      inv := ⟨TopCat.ofHom { toFun := e.symm, continuous_toFun := e.symm.continuous }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro p
        change e.symm (e p) = p
        exact e.symm_apply_apply p
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro p
        change e (e.symm p) = p
        exact e.apply_symm_apply p }

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHausIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHaus
      D α a b t hjoint ≅
    compactIndexedObservationRangeCompHausLimitFixedPointCompHaus D α t.1 := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isCompact_fiber
        D α a b t hjoint)
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t.1) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet D α t.1)
  let e := compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberHomeomorph
    D α a b t
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) ≅
    CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t.1)
  exact
    { hom := ⟨TopCat.ofHom { toFun := e, continuous_toFun := e.continuous }⟩
      inv := ⟨TopCat.ofHom { toFun := e.symm, continuous_toFun := e.symm.continuous }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro p
        change e.symm (e p) = p
        exact e.symm_apply_apply p
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro p
        change e (e.symm p) = p
        exact e.apply_symm_apply p }

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHaus
      D α a b t hjoint ⟶
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOnCompHaus
        D α a b hjoint := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isCompact_fiber
        D α a b t hjoint)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t) ⟶
    CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b)
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHaus
      D α a b t hjoint ⟶
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOnCompHaus
        D α a b hjoint := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isCompact_fiber
        D α a b t hjoint)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t) ⟶
    CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b)
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion_carrier_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hjoint ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier
          D α a b hjoint =
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHausIso
        D α a b t hjoint).hom ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointInclusion D α t.1 := by
  apply ConcreteCategory.hom_ext
  intro p
  change p.1.1.2 = p.1.1.2
  rfl

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion_carrier_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hjoint ≫
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier
          D α a b hjoint =
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHausIso
        D α a b t hjoint).hom ≫
        compactIndexedObservationRangeCompHausLimitFixedPointInclusion D α t.1 := by
  apply ConcreteCategory.hom_ext
  intro p
  change p.1.1.2 = p.1.1.2
  rfl

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPoint_time
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus D α t.1 ⟶
      CompHaus.of (Set.Icc a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t.1) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet D α t.1)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t.1) ⟶
    CompHaus.of (Set.Icc a b)
  exact ⟨TopCat.ofHom
    { toFun := fun _ => t
      continuous_toFun := continuous_const }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPoint_time
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    compactIndexedObservationRangeCompHausLimitFixedPointCompHaus D α t.1 ⟶
      CompHaus.of (Set.Icc a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t.1) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet D α t.1)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t.1) ⟶
    CompHaus.of (Set.Icc a b)
  exact ⟨TopCat.ofHom
    { toFun := fun _ => t
      continuous_toFun := continuous_const }⟩

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion_time_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hjoint ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time
          D α a b hjoint =
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHausIso
        D α a b t hjoint).hom ≫
        compactIndexedObservationQuotientCompHausLimitFixedPoint_time D α a b t := by
  apply ConcreteCategory.hom_ext
  intro p
  have hp := p.2
  unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber at hp
  change (p.1.1.1 : ℝ) = (t : ℝ) at hp
  exact Subtype.ext hp

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion_time_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hjoint ≫
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time
          D α a b hjoint =
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHausIso
        D α a b t hjoint).hom ≫
        compactIndexedObservationRangeCompHausLimitFixedPoint_time D α a b t := by
  apply ConcreteCategory.hom_ext
  intro p
  have hp := p.2
  unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber at hp
  change (p.1.1.1 : ℝ) = (t : ℝ) at hp
  exact Subtype.ext hp

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    _root_.Topology.IsClosedEmbedding
      ((↑) : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t →
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) := by
  exact Topology.IsClosedEmbedding.subtypeVal
    (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isClosed_fiber
      D α a b t)

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b) :
    _root_.Topology.IsClosedEmbedding
      ((↑) : compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t →
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) := by
  exact Topology.IsClosedEmbedding.subtypeVal
    (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isClosed_fiber
      D α a b t)

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion_injective
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    Function.Injective
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hjoint) := by
  intro p q h
  exact Subtype.ext h

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion_injective
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) (t : Set.Icc a b)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    Function.Injective
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hjoint) := by
  intro p q h
  exact Subtype.ext h

end InfoGeometry.Topology
