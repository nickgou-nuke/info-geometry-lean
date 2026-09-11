import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitOrbitClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff orbit closures for varying-carrier quotient limits

The ambient limit action is an actual `CompHaus` isomorphism.  Its restriction
to the native topological orbit closure is constructed explicitly; compactness
comes from closedness inside the compact inverse-limit carrier.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimitActionHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimit D ≃ₜ
      compactIndexedObservationQuotientCompHausLimit D := by
  let e := compactIndexedObservationQuotientCompHausLimitActionIso
    D α hα0 hαadd t
  exact
    { toFun := e.hom
      invFun := e.inv
      left_inv := by
        intro x
        have h := congrArg (fun f => f x) e.hom_inv_id
        simpa using h
      right_inv := by
        intro x
        have h := congrArg (fun f => f x) e.inv_hom_id
        simpa using h
      continuous_toFun := e.hom.hom.hom'.continuous
      continuous_invFun := e.inv.hom.hom'.continuous }

theorem compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitActionHomeomorph
        D α hα0 hαadd s ''
        compactIndexedObservationQuotientCompHausLimitOrbit D α x =
      compactIndexedObservationQuotientCompHausLimitOrbit D α
        (compactIndexedObservationQuotientCompHausLimitAction D α s x) := by
  change compactIndexedObservationQuotientCompHausLimitAction D α s ''
      compactIndexedObservationQuotientCompHausLimitOrbit D α x = _
  exact compactIndexedObservationQuotientCompHausLimit_action_image_orbit
    D α hαadd s x

theorem compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitActionHomeomorph
        D α hα0 hαadd s ''
        compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x =
      compactIndexedObservationQuotientCompHausLimitOrbitClosure D α
        (compactIndexedObservationQuotientCompHausLimitAction D α s x) := by
  rw [compactIndexedObservationQuotientCompHausLimitOrbitClosure,
    compactIndexedObservationQuotientCompHausLimitOrbitClosure]
  rw [(compactIndexedObservationQuotientCompHausLimitActionHomeomorph
    D α hα0 hαadd s).image_closure]
  exact congrArg closure
    (compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbit
      D α hα0 hαadd s x)

abbrev compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :=
  {y // y ∈ compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x}

noncomputable def compactIndexedObservationQuotientCompHausLimitOrbitClosureCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) : CompHaus := by
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_orbitClosure D α x)
  exact CompHaus.of
    (compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x)

noncomputable def compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x ≃ₜ
      compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α
        (compactIndexedObservationQuotientCompHausLimitAction D α t x) := by
  let h_orbit := compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbitClosure
    D α hα0 hαadd t x
  exact
    { toFun := fun y => ⟨
          compactIndexedObservationQuotientCompHausLimitAction D α t y.1, by
          rw [← h_orbit]
          exact ⟨y.1, y.2, rfl⟩⟩
      invFun := fun y => ⟨
          compactIndexedObservationQuotientCompHausLimitAction D α (-t) y.1, by
          have h := compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbitClosure
            D α hα0 hαadd (-t) (compactIndexedObservationQuotientCompHausLimitAction D α t x)
          have hcancel := congrArg (fun f => f x)
            (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd t (-t))
          rw [add_neg_cancel,
            compactIndexedObservationQuotientCompHausLimitAction_zero D α hα0] at hcancel
          have hx :
              compactIndexedObservationQuotientCompHausLimitAction D α (-t)
                  (compactIndexedObservationQuotientCompHausLimitAction D α t x) = x := by
            simpa using hcancel.symm
          rw [hx] at h
          rw [← h]
          exact ⟨y.1, y.2, rfl⟩⟩
      left_inv := by
        intro y
        apply Subtype.ext
        have h := congrArg (fun f => f y.1)
          (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd t (-t))
        rw [add_neg_cancel,
          compactIndexedObservationQuotientCompHausLimitAction_zero D α hα0] at h
        simpa using h.symm
      right_inv := by
        intro y
        apply Subtype.ext
        have h := congrArg (fun f => f y.1)
          (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd (-t) t)
        rw [neg_add_cancel,
          compactIndexedObservationQuotientCompHausLimitAction_zero D α hα0] at h
        simpa using h.symm
      continuous_toFun :=
        (compactIndexedObservationQuotientCompHausLimitActionHomeomorph
          D α hα0 hαadd t).continuous_toFun.comp continuous_subtype_val |>.subtype_mk
            (fun y => by
              rw [← h_orbit]
              exact ⟨y.1, y.2, rfl⟩)
      continuous_invFun :=
        (compactIndexedObservationQuotientCompHausLimitActionHomeomorph
          D α hα0 hαadd (-t)).continuous_toFun.comp continuous_subtype_val |>.subtype_mk
            (fun y => by
              have h := compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbitClosure
                D α hα0 hαadd (-t)
                  (compactIndexedObservationQuotientCompHausLimitAction D α t x)
              have hcancel := congrArg (fun f => f x)
                (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd t (-t))
              rw [add_neg_cancel,
                compactIndexedObservationQuotientCompHausLimitAction_zero D α hα0] at hcancel
              have hx :
                  compactIndexedObservationQuotientCompHausLimitAction D α (-t)
                      (compactIndexedObservationQuotientCompHausLimitAction D α t x) = x := by
                simpa using hcancel.symm
              rw [hx] at h
              rw [← h]
              exact ⟨y.1, y.2, rfl⟩) }

noncomputable def compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitOrbitClosureCompHaus D α x ≅
      compactIndexedObservationQuotientCompHausLimitOrbitClosureCompHaus D α
        (compactIndexedObservationQuotientCompHausLimitAction D α t x) := by
  let e := compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowHomeomorph
    D α hα0 hαadd x t
  exact
    { hom := ⟨TopCat.ofHom
          { toFun := e
            continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
          { toFun := e.symm
            continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e.symm (e y) = y
        exact e.symm_apply_apply y
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso_hom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (t : ℝ)
    (y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x) :
    (compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso
      D α hα0 hαadd x t).hom y =
      compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowHomeomorph
        D α hα0 hαadd x t y :=
  rfl

theorem compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso_comp_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (s t : ℝ)
    (y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x) :
    (((compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso
      D α hα0 hαadd x s).hom ≫
        (compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso
          D α hα0 hαadd
          (compactIndexedObservationQuotientCompHausLimitAction D α s x) t).hom) y).1 =
      ((compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso
        D α hα0 hαadd x (t + s)).hom y).1 := by
  change
    (compactIndexedObservationQuotientCompHausLimitAction D α t)
        ((compactIndexedObservationQuotientCompHausLimitAction D α s) y.1) =
      (compactIndexedObservationQuotientCompHausLimitAction D α (t + s)) y.1
  have h := congrArg (fun f => f y.1)
    (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s t)
  simpa [add_comm] using h.symm

theorem compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso_comp
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (s t : ℝ) :
    let harg :
        compactIndexedObservationQuotientCompHausLimitAction D α t
            (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
          compactIndexedObservationQuotientCompHausLimitAction D α (t + s) x := by
      have h := congrArg (fun f => f x)
        (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s t)
      simpa [add_comm] using h.symm
    let hset := congrArg
      (fun z => compactIndexedObservationQuotientCompHausLimitOrbitClosure D α z)
      harg
    let e :=
      (compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowHomeomorph
        D α hα0 hαadd x s).trans
        ((compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowHomeomorph
          D α hα0 hαadd
          (compactIndexedObservationQuotientCompHausLimitAction D α s x) t).trans
          (Homeomorph.setCongr hset))
    (CompHausLike.isoOfHomeo e).hom =
      (compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso
        D α hα0 hαadd x (t + s)).hom := by
  dsimp
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  simpa [Category.assoc] using
    compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowIso_comp_apply
      D α hα0 hαadd x s t y

end InfoGeometry.Topology
