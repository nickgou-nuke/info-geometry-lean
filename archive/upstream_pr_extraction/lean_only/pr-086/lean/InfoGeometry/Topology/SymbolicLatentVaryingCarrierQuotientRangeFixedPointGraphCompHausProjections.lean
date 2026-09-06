import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointGraphCompHaus

/-!
# Projections of compact fixed-point graphs

The compact graph carriers have the two canonical continuous projections: the
time projection to the compact interval and the carrier projection to the
quotient or observation-range limit.  These are genuine `CompHaus` morphisms.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOnCompHaus
      D α a b hjoint ⟶ CompHaus.of (Set.Icc a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) ⟶
    CompHaus.of (Set.Icc a b)
  exact ⟨TopCat.ofHom
    { toFun := fun p => p.1.1
      continuous_toFun :=
        continuous_fst.comp continuous_subtype_val }⟩

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOnCompHaus
      D α a b hjoint ⟶ CompHaus.of (compactIndexedObservationQuotientCompHausLimit D) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) ⟶
    CompHaus.of (compactIndexedObservationQuotientCompHausLimit D)
  exact ⟨TopCat.ofHom
    { toFun := fun p => p.1.2
      continuous_toFun :=
        continuous_snd.comp continuous_subtype_val }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOnCompHaus
      D α a b hjoint ⟶ CompHaus.of (Set.Icc a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) ⟶
    CompHaus.of (Set.Icc a b)
  exact ⟨TopCat.ofHom
    { toFun := fun p => p.1.1
      continuous_toFun :=
        continuous_fst.comp continuous_subtype_val }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOnCompHaus
      D α a b hjoint ⟶ CompHaus.of (compactIndexedObservationRangeCompHausLimit D) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hjoint)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) ⟶
    CompHaus.of (compactIndexedObservationRangeCompHausLimit D)
  exact ⟨TopCat.ofHom
    { toFun := fun p => p.1.2
      continuous_toFun :=
        continuous_snd.comp continuous_subtype_val }⟩

@[simp] theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (p : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn
      D α a b) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time
      D α a b hjoint p = p.1.1 := by
  rfl

@[simp] theorem compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (p : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn
      D α a b) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier
      D α a b hjoint p = p.1.2 := by
  rfl

@[simp] theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (p : compactIndexedObservationRangeCompHausLimitFixedPointGraphOn
      D α a b) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time
      D α a b hjoint p = p.1.1 := by
  rfl

@[simp] theorem compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (p : compactIndexedObservationRangeCompHausLimitFixedPointGraphOn
      D α a b) :
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier
      D α a b hjoint p = p.1.2 := by
  rfl

end InfoGeometry.Topology
