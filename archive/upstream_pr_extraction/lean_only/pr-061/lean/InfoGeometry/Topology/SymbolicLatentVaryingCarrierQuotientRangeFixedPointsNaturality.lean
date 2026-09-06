import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointsCompHaus
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointsFlow
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeOrbitClosureCompHausNaturality

/-!
# Quotient-range naturality on fixed-point loci

The canonical quotient-range Homeomorph restricts to the fixed points of
every time slice.  This file proves the restriction directly and packages it
as a native `CompHaus` isomorphism.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientRangeFixedPointHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t ≃ₜ
      compactIndexedObservationRangeCompHausLimitFixedPointSet D α t := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
  refine
    { toFun := fun x =>
        ⟨e x.1, ?_⟩
      invFun := fun y =>
        ⟨e.symm y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ } 
  · change compactIndexedObservationRangeCompHausLimitAction D α t (e x.1) = e x.1
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd t x.1
    calc
      compactIndexedObservationRangeCompHausLimitAction D α t (e x.1) =
          e (compactIndexedObservationQuotientCompHausLimitAction D α t x.1) := h.symm
      _ = e x.1 := by rw [x.2]
  · change compactIndexedObservationQuotientCompHausLimitAction D α t (e.symm y.1) = e.symm y.1
    apply e.injective
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd t (e.symm y.1)
    calc
      e (compactIndexedObservationQuotientCompHausLimitAction D α t (e.symm y.1)) =
          compactIndexedObservationRangeCompHausLimitAction D α t (e (e.symm y.1)) := h
      _ = compactIndexedObservationRangeCompHausLimitAction D α t y.1 := by
        rw [e.apply_symm_apply]
      _ = y.1 := y.2
      _ = e (e.symm y.1) := by rw [e.apply_symm_apply]
  · intro x
    apply Subtype.ext
    exact e.left_inv x.1
  · intro y
    apply Subtype.ext
    exact e.right_inv y.1
  · exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  · exact (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem compactIndexedObservationQuotientRangeFixedPointHomeomorph_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationQuotientRangeFixedPointHomeomorph D α hα0 hαadd t x =
      ⟨compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x.1, by
        change compactIndexedObservationRangeCompHausLimitAction D α t
          (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x.1) =
          compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x.1
        have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
          D α hα0 hαadd t x.1
        rw [← h, x.2]⟩ :=
  rfl

noncomputable def compactIndexedObservationQuotientRangeFixedPointCompHausIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus D α t ≅
      compactIndexedObservationRangeCompHausLimitFixedPointCompHaus D α t := by
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet D α t)
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet D α t)
  let e := compactIndexedObservationQuotientRangeFixedPointHomeomorph
    D α hα0 hαadd t
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) ≅
    CompHaus.of (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t)
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

@[simp] theorem compactIndexedObservationQuotientRangeFixedPointCompHausIso_hom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    (compactIndexedObservationQuotientRangeFixedPointCompHausIso
      D α hα0 hαadd t).hom x =
      compactIndexedObservationQuotientRangeFixedPointHomeomorph D α hα0 hαadd t x :=
  rfl

theorem compactIndexedObservationQuotientRangeFixedPointHomeomorph_action
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t s : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t
        (s,
          compactIndexedObservationQuotientRangeFixedPointHomeomorph
            D α hα0 hαadd t x) =
      compactIndexedObservationQuotientRangeFixedPointHomeomorph
        D α hα0 hαadd t
        (compactIndexedObservationQuotientCompHausLimitFixedPointAction
          D α hαadd t (s, x)) := by
  apply Subtype.ext
  change compactIndexedObservationRangeCompHausLimitAction D α s
      (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x.1) =
    compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
      (compactIndexedObservationQuotientCompHausLimitAction D α s x.1)
  exact (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
    D α hα0 hαadd s x.1).symm

theorem compactIndexedObservationQuotientRangeFixedPointCompHausIso_hom_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (t s : ℝ) :
    (compactIndexedObservationQuotientRangeFixedPointCompHausIso
      D α hα0 hαadd t).hom ≫
        compactIndexedObservationRangeCompHausLimitFixedPointActionCompHausHom
          D α hαadd hrange t s =
      compactIndexedObservationQuotientCompHausLimitFixedPointActionCompHausHom
          D α hαadd hquotient t s ≫
        (compactIndexedObservationQuotientRangeFixedPointCompHausIso
          D α hα0 hαadd t).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  change
    compactIndexedObservationRangeCompHausLimitFixedPointAction
        D α hαadd t
        (s,
          compactIndexedObservationQuotientRangeFixedPointHomeomorph
            D α hα0 hαadd t x) =
      compactIndexedObservationQuotientRangeFixedPointHomeomorph
        D α hα0 hαadd t
        (compactIndexedObservationQuotientCompHausLimitFixedPointAction
          D α hαadd t (s, x))
  exact compactIndexedObservationQuotientRangeFixedPointHomeomorph_action
    D α hα0 hαadd t s x

end InfoGeometry.Topology
