import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitOrbitClosureCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierCompHausLimitOrbitClosureCompHaus

/-!
# Quotient-range naturality on orbit closures

The quotient and observation-range inverse limits are canonically isomorphic.
This owner proves that the isomorphism transports the native orbit and orbit
closure, using the action naturality theorem on the ambient limits.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientRangeCompHausLimitHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationQuotientCompHausLimit D ≃ₜ
      compactIndexedObservationRangeCompHausLimit D := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitIso D
  exact
    { toFun := e.hom
      invFun := e.inv
      left_inv := by
        intro x
        have h := congrArg (fun f => f x) e.hom_inv_id
        simpa using h
      right_inv := by
        intro y
        have h := congrArg (fun f => f y) e.inv_hom_id
        simpa using h
      continuous_toFun := e.hom.hom.hom'.continuous
      continuous_invFun := e.inv.hom.hom'.continuous }

theorem compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
        (compactIndexedObservationQuotientCompHausLimitAction D α t x) =
      compactIndexedObservationRangeCompHausLimitAction D α t
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) := by
  let h := compactIndexedObservationQuotientRangeCompHausLimitIso_actionIso_naturality
    D α hα0 hαadd t
  have hx := congrArg (fun f => f x) h
  simpa using hx

theorem compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_image_orbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D ''
        compactIndexedObservationQuotientCompHausLimitOrbit D α x =
      compactIndexedObservationRangeCompHausLimitOrbit D α
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    exact (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd t x).symm
  · rintro ⟨t, rfl⟩
    refine ⟨compactIndexedObservationQuotientCompHausLimitAction D α t x,
      ⟨t, rfl⟩, ?_⟩
    exact compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd t x

theorem compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_image_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D ''
        compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x =
      compactIndexedObservationRangeCompHausLimitOrbitClosure D α
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) := by
  rw [compactIndexedObservationQuotientCompHausLimitOrbitClosure,
    compactIndexedObservationRangeCompHausLimitOrbitClosure]
  rw [(compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).image_closure]
  exact congrArg closure
    (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_image_orbit
      D α hα0 hαadd x)

abbrev compactIndexedObservationQuotientRangeOrbitClosureCarrier
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :=
  {y // y ∈ compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x}

abbrev compactIndexedObservationRangeQuotientRangeOrbitClosureCarrier
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :=
  {y // y ∈ compactIndexedObservationRangeCompHausLimitOrbitClosure D α
      (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x)}

noncomputable def compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientRangeOrbitClosureCarrier D α x ≃ₜ
      compactIndexedObservationRangeQuotientRangeOrbitClosureCarrier D α x := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
  let h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_image_orbitClosure
    D α hα0 hαadd x
  exact
    { toFun := fun y => ⟨e y.1, by
          rw [← h]
          exact ⟨y.1, y.2, rfl⟩⟩
      invFun := fun y => ⟨e.symm y.1, by
        have hy : y.1 ∈ e ''
            compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x := by
          rw [h]
          exact y.2
        rcases hy with ⟨z, hz, hzy⟩
        have hz' : e.symm y.1 = z := by
          rw [← hzy]
          exact e.symm_apply_apply z
        rw [hz']
        exact hz⟩
      left_inv := by
        intro y
        apply Subtype.ext
        exact e.symm_apply_apply y.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y.1
      continuous_toFun :=
        e.continuous_toFun.comp continuous_subtype_val |>.subtype_mk
          (fun y => by
            rw [← h]
            exact ⟨y.1, y.2, rfl⟩)
      continuous_invFun := by
        exact (e.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk
          (fun y => by
            change e.symm y.1 ∈
              compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x
            have hy : y.1 ∈ e ''
                compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x := by
              rw [h]
              exact y.2
            rcases hy with ⟨z, hz, hzy⟩
            have hz' : e.symm y.1 = z := by
              rw [← hzy]
              exact e.symm_apply_apply z
            rw [hz']
            exact hz) }

end InfoGeometry.Topology
