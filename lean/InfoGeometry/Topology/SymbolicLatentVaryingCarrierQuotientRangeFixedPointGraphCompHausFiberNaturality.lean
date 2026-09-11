import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointGraphCompHausFiber
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Naturality of compact graph fibers

The quotient-range fixed-point isomorphism and the bounded graph
quotient-range isomorphism agree on every time fiber.  This is the native
`CompHaus` naturality square for the closed fiber subobjects.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

theorem compactIndexedObservationQuotientRangeFixedPointGraphOn_fiberCompHausIso_square
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ) (t : Set.Icc a b)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberCompHausIso
      D α a b t hquotient).hom ≫
        (compactIndexedObservationQuotientRangeFixedPointCompHausIso
          D α hα0 hαadd t.1).hom ≫
        (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberCompHausIso
          D α a b t hrange).inv ≫
        (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion
          D α a b t hrange) =
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion
        D α a b t hquotient) ≫
        (compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
          D α hα0 hαadd a b hquotient hrange).hom := by
  apply ConcreteCategory.hom_ext
  intro p
  change
    (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberHomeomorph
        D α a b t).symm
      ((compactIndexedObservationQuotientRangeFixedPointCompHausIso
        D α hα0 hαadd t.1).hom
        (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberHomeomorph
          D α a b t p)) =
      compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
        D α hα0 hαadd a b hquotient hrange p.1
  rw [compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberHomeomorph_apply,
    compactIndexedObservationQuotientRangeFixedPointCompHausIso_hom_apply]
  unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberHomeomorph
  unfold compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
  unfold compactIndexedObservationQuotientRangeFixedPointHomeomorph
  dsimp
  apply Subtype.ext
  apply Prod.ext
  · have hp := p.2
    unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber at hp
    change (p.1.1.1 : ℝ) = (t : ℝ) at hp
    exact Subtype.ext hp.symm
  · rfl

theorem compactIndexedObservationQuotientRangeFixedPointGraphOn_transport_fiber_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ) (t : Set.Icc a b)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    _root_.Topology.IsClosedEmbedding (fun p :
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t =>
      compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
        D α hα0 hαadd a b hquotient hrange p.1) := by
  simpa only [Function.comp_apply] using
    (compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
      D α hα0 hαadd a b hquotient hrange).isClosedEmbedding.comp
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiberInclusion_isClosedEmbedding
        D α a b t)

theorem compactIndexedObservationQuotientRangeFixedPointGraphOn_transport_fiber_isClosedEmbedding_symm
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ) (t : Set.Icc a b)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    _root_.Topology.IsClosedEmbedding (fun p :
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
        D α a b t =>
      (compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
        D α hα0 hαadd a b hquotient hrange).symm p.1) := by
  simpa only [Function.comp_apply] using
    (compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
      D α hα0 hαadd a b hquotient hrange).symm.isClosedEmbedding.comp
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiberInclusion_isClosedEmbedding
        D α a b t)

theorem compactIndexedObservationQuotientRangeFixedPointGraphOn_transport_fiber_range_eq
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ) (t : Set.Icc a b)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    Set.range (fun p :
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
        D α a b t =>
      compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
        D α hα0 hαadd a b hquotient hrange p.1) =
      Set.range (fun p :
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
          D α a b t => p.1) := by
  let e := compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
    D α hα0 hαadd a b hquotient hrange
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨⟨e p.1, ?_⟩, rfl⟩
    have hp := p.2
    unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber at hp
    change (p.1.1.1 : ℝ) = (t : ℝ) at hp
    unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber
    change (p.1.1.1 : ℝ) = (t : ℝ)
    exact hp
  · rintro ⟨p, rfl⟩
    refine ⟨⟨e.symm p.1, ?_⟩, ?_⟩
    · have hp := p.2
      unfold compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_fiber at hp
      change (p.1.1.1 : ℝ) = (t : ℝ) at hp
      unfold compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_fiber
      change (p.1.1.1 : ℝ) = (t : ℝ)
      exact hp
    · exact e.apply_symm_apply p.1

end InfoGeometry.Topology
