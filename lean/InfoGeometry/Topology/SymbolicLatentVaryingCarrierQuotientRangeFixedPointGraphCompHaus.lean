import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointGraph
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compact fixed-point graphs on bounded time intervals

Restricting time to a compact interval turns the closed fixed-point graph into
a compact Hausdorff carrier.  The construction is made separately for the
quotient and observation-range limits.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) : Set
      (Set.Icc a b × compactIndexedObservationQuotientCompHausLimit D) :=
  {p | compactIndexedObservationQuotientCompHausLimitAction D α p.1.1 p.2 = p.2}

def compactIndexedObservationRangeCompHausLimitFixedPointGraphOn
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ) : Set
      (Set.Icc a b × compactIndexedObservationRangeCompHausLimit D) :=
  {p | compactIndexedObservationRangeCompHausLimitAction D α p.1.1 p.2 = p.2}

set_option maxHeartbeats 1000000 in
theorem compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointGraphOn
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    IsClosed
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) := by
  have hinput : Continuous (fun p : Set.Icc a b ×
      compactIndexedObservationQuotientCompHausLimit D =>
        (p.1.1, p.2)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have haction : Continuous (fun p : Set.Icc a b ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1.1 p.2) := by
    simpa only [Function.comp_apply] using hjoint.comp hinput
  exact isClosed_eq haction continuous_snd

set_option maxHeartbeats 1000000 in
theorem compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointGraphOn
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    IsClosed
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) := by
  have hinput : Continuous (fun p : Set.Icc a b ×
      compactIndexedObservationRangeCompHausLimit D =>
        (p.1.1, p.2)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have haction : Continuous (fun p : Set.Icc a b ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1.1 p.2) := by
    simpa only [Function.comp_apply] using hjoint.comp hinput
  exact isClosed_eq haction continuous_snd

theorem compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    IsCompact
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointGraphOn
      D α a b hjoint)
    (Set.subset_univ _)

theorem compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    IsCompact
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointGraphOn
      D α a b hjoint)
    (Set.subset_univ _)

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointGraphOnCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
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
  exact CompHaus.of
    (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b)

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointGraphOnCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (a b : ℝ)
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
  exact CompHaus.of
    (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b)

end InfoGeometry.Topology
