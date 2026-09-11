import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointGraphCompHausProjections
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compact graph embeddings

The compact fixed-point graph is a genuine closed subobject of the compact
time-carrier product.  This file records its inclusion and the two projection
factorizations for both carrier realizations.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_productFst
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) (a b : ℝ) :
    CompHaus.of
        (Set.Icc a b × compactIndexedObservationQuotientCompHausLimit D) ⟶
      CompHaus.of (Set.Icc a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact ⟨TopCat.ofHom
    { toFun := Prod.fst
      continuous_toFun := continuous_fst }⟩

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_productSnd
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) (a b : ℝ) :
    CompHaus.of
        (Set.Icc a b × compactIndexedObservationQuotientCompHausLimit D) ⟶
      CompHaus.of (compactIndexedObservationQuotientCompHausLimit D) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact ⟨TopCat.ofHom
    { toFun := Prod.snd
      continuous_toFun := continuous_snd }⟩

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOnCompHaus
      D α a b hjoint ⟶
      CompHaus.of (Set.Icc a b × compactIndexedObservationQuotientCompHausLimit D) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) ⟶
    CompHaus.of (Set.Icc a b × compactIndexedObservationQuotientCompHausLimit D)
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_productFst
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) (a b : ℝ) :
    CompHaus.of
        (Set.Icc a b × compactIndexedObservationRangeCompHausLimit D) ⟶
      CompHaus.of (Set.Icc a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact ⟨TopCat.ofHom
    { toFun := Prod.fst
      continuous_toFun := continuous_fst }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_productSnd
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) (a b : ℝ) :
    CompHaus.of
        (Set.Icc a b × compactIndexedObservationRangeCompHausLimit D) ⟶
      CompHaus.of (compactIndexedObservationRangeCompHausLimit D) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact ⟨TopCat.ofHom
    { toFun := Prod.snd
      continuous_toFun := continuous_snd }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOnCompHaus
      D α a b hjoint ⟶
      CompHaus.of (Set.Icc a b × compactIndexedObservationRangeCompHausLimit D) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) ⟶
    CompHaus.of (Set.Icc a b × compactIndexedObservationRangeCompHausLimit D)
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion_fst
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion
        D α a b hjoint ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_productFst D a b =
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time
        D α a b hjoint := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion_snd
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion
        D α a b hjoint ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_productSnd D a b =
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier
        D α a b hjoint := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion_fst
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion
        D α a b hjoint ≫
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_productFst D a b =
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time
        D α a b hjoint := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion_snd
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion
        D α a b hjoint ≫
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_productSnd D a b =
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier
        D α a b hjoint := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    _root_.Topology.IsClosedEmbedding
      ((↑) : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn
        D α a b → Set.Icc a b × compactIndexedObservationQuotientCompHausLimit D) := by
  exact Topology.IsClosedEmbedding.subtypeVal
    (compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointGraphOn
      D α a b hjoint)

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    _root_.Topology.IsClosedEmbedding
      ((↑) : compactIndexedObservationRangeCompHausLimitFixedPointGraphOn
        D α a b → Set.Icc a b × compactIndexedObservationRangeCompHausLimit D) := by
  exact Topology.IsClosedEmbedding.subtypeVal
    (compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointGraphOn
      D α a b hjoint)

theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion_injective
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    Function.Injective
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_inclusion
        D α a b hjoint) := by
  intro p q h
  exact Subtype.ext h

theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion_injective
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    Function.Injective
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_inclusion
        D α a b hjoint) := by
  intro p q h
  exact Subtype.ext h

end InfoGeometry.Topology
