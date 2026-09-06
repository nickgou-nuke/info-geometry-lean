import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointGraphCompHausEmbedding

/-!
# Quotient-range naturality of compact fixed-point graphs

The canonical quotient-range homeomorphism transports the bounded fixed-point
graph, not only each individual fixed-point fiber.  The time coordinate is
unchanged, while the carrier coordinate is transported by the native
quotient-range homeomorphism.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b ≃ₜ
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
  refine
    { toFun := fun p =>
        ⟨(p.1.1, e p.1.2), ?_⟩
      invFun := fun p =>
        ⟨(p.1.1, e.symm p.1.2), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change compactIndexedObservationRangeCompHausLimitAction D α p.1.1
      (e p.1.2) = e p.1.2
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd p.1.1 p.1.2
    calc
      compactIndexedObservationRangeCompHausLimitAction D α p.1.1
          (e p.1.2) = e (compactIndexedObservationQuotientCompHausLimitAction
            D α p.1.1 p.1.2) := h.symm
      _ = e p.1.2 := by rw [p.2]
  · change compactIndexedObservationQuotientCompHausLimitAction D α p.1.1
      (e.symm p.1.2) = e.symm p.1.2
    apply e.injective
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd p.1.1 (e.symm p.1.2)
    calc
      e (compactIndexedObservationQuotientCompHausLimitAction D α p.1.1
          (e.symm p.1.2)) = compactIndexedObservationRangeCompHausLimitAction
            D α p.1.1 (e (e.symm p.1.2)) := h
      _ = compactIndexedObservationRangeCompHausLimitAction D α p.1.1 p.1.2 := by
        rw [e.apply_symm_apply]
      _ = p.1.2 := p.2
      _ = e (e.symm p.1.2) := by rw [e.apply_symm_apply]
  · intro p
    apply Subtype.ext
    exact Prod.ext rfl (e.left_inv p.1.2)
  · intro p
    apply Subtype.ext
    exact Prod.ext rfl (e.right_inv p.1.2)
  · exact
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (e.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  · exact
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (e.symm.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

@[simp] theorem compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (p : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :
    compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
      D α hα0 hαadd a b hquotient hrange p =
      ⟨(p.1.1, compactIndexedObservationQuotientRangeCompHausLimitHomeomorph
        D p.1.2), by
        change compactIndexedObservationRangeCompHausLimitAction D α p.1.1
          (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D p.1.2) =
          compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D p.1.2
        have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
          D α hα0 hαadd p.1.1 p.1.2
        rw [← h, p.2]⟩ := rfl

noncomputable def compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    compactIndexedObservationQuotientCompHausLimitFixedPointGraphOnCompHaus
      D α a b hquotient ≅
    compactIndexedObservationRangeCompHausLimitFixedPointGraphOnCompHaus
      D α a b hrange := by
  letI : CompactSpace (Set.Icc a b) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hquotient)
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointGraphOn
        D α a b hrange)
  let e := compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
    D α hα0 hαadd a b hquotient hrange
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) ≅
    CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointGraphOn D α a b)
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous }⟩
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

@[simp] theorem compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso_hom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2))
    (p : compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn D α a b) :
    (compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
      D α hα0 hαadd a b hquotient hrange).hom p =
      compactIndexedObservationQuotientRangeFixedPointGraphOnHomeomorph
        D α hα0 hαadd a b hquotient hrange p := rfl

theorem compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso_hom_time_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    (compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
      D α hα0 hαadd a b hquotient hrange).hom ≫
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time
          D α a b hrange =
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time
        D α a b hquotient := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso_hom_carrier_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    (compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
      D α hα0 hαadd a b hquotient hrange).hom ≫
        compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier
          D α a b hrange =
      compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier
          D α a b hquotient ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso_inv_time_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    (compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
      D α hα0 hαadd a b hquotient hrange).inv ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_time
          D α a b hquotient =
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_time
          D α a b hrange ≫
        𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

theorem compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso_inv_carrier_natural
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (a b : ℝ)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2))
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    (compactIndexedObservationQuotientRangeFixedPointGraphOnCompHausIso
      D α hα0 hαadd a b hquotient hrange).inv ≫
        compactIndexedObservationQuotientCompHausLimitFixedPointGraphOn_carrier
          D α a b hquotient =
      compactIndexedObservationRangeCompHausLimitFixedPointGraphOn_carrier
          D α a b hrange ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso D).inv := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

end InfoGeometry.Topology
