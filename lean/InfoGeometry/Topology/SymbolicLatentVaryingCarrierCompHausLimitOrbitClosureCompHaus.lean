import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitActionIso
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff orbit closures for varying-carrier range limits

The ambient limit action is an actual `CompHaus` isomorphism.  Its restriction
to the native topological orbit closure is constructed explicitly; compactness
comes from closedness inside the compact inverse-limit carrier.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationRangeCompHausLimitOrbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) : Set
      (compactIndexedObservationRangeCompHausLimit D) :=
  Set.range (fun t : ℝ =>
    compactIndexedObservationRangeCompHausLimitAction D α t x)

def compactIndexedObservationRangeCompHausLimitOrbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) : Set
      (compactIndexedObservationRangeCompHausLimit D) :=
  closure (compactIndexedObservationRangeCompHausLimitOrbit D α x)

theorem compactIndexedObservationRangeCompHausLimit_isClosed_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :
    IsClosed (compactIndexedObservationRangeCompHausLimitOrbitClosure D α x) := by
  exact isClosed_closure

theorem compactIndexedObservationRangeCompHausLimit_orbit_subset_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitOrbit D α x ⊆
      compactIndexedObservationRangeCompHausLimitOrbitClosure D α x := by
  exact subset_closure

theorem compactIndexedObservationRangeCompHausLimit_initial_mem_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (x : compactIndexedObservationRangeCompHausLimit D) :
    x ∈ compactIndexedObservationRangeCompHausLimitOrbitClosure D α x := by
  apply compactIndexedObservationRangeCompHausLimit_orbit_subset_orbitClosure D α x
  refine ⟨0, ?_⟩
  change (compactIndexedObservationRangeCompHausLimitAction D α 0) x = x
  rw [compactIndexedObservationRangeCompHausLimitAction_zero D α hα0]
  rfl

theorem compactIndexedObservationRangeCompHausLimit_isCompact_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :
    IsCompact (compactIndexedObservationRangeCompHausLimitOrbitClosure D α x) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationRangeCompHausLimit_isClosed_orbitClosure D α x)
    (Set.subset_univ _)

theorem compactIndexedObservationRangeCompHausLimit_action_image_orbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitAction D α s ''
        compactIndexedObservationRangeCompHausLimitOrbit D α x =
      compactIndexedObservationRangeCompHausLimitOrbit D α
        (compactIndexedObservationRangeCompHausLimitAction D α s x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    change
      (compactIndexedObservationRangeCompHausLimitAction D α t)
          (compactIndexedObservationRangeCompHausLimitAction D α s x) =
        (compactIndexedObservationRangeCompHausLimitAction D α s)
          (compactIndexedObservationRangeCompHausLimitAction D α t x)
    have hst := congrArg (fun f => f x)
      (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s t)
    have hts := congrArg (fun f => f x)
      (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd t s)
    calc
      (compactIndexedObservationRangeCompHausLimitAction D α t)
          (compactIndexedObservationRangeCompHausLimitAction D α s x) =
          (compactIndexedObservationRangeCompHausLimitAction D α (s + t)) x := by
            simpa using hst.symm
      _ = (compactIndexedObservationRangeCompHausLimitAction D α (t + s)) x := by
            rw [add_comm]
      _ = (compactIndexedObservationRangeCompHausLimitAction D α s)
          (compactIndexedObservationRangeCompHausLimitAction D α t x) := by
            simpa using hts
  · rintro ⟨t, rfl⟩
    refine ⟨compactIndexedObservationRangeCompHausLimitAction D α t x,
      ⟨t, rfl⟩, ?_⟩
    change
      (compactIndexedObservationRangeCompHausLimitAction D α s)
          (compactIndexedObservationRangeCompHausLimitAction D α t x) =
        (compactIndexedObservationRangeCompHausLimitAction D α t)
          (compactIndexedObservationRangeCompHausLimitAction D α s x)
    have hst := congrArg (fun f => f x)
      (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s t)
    have hts := congrArg (fun f => f x)
      (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd t s)
    calc
      (compactIndexedObservationRangeCompHausLimitAction D α s)
          (compactIndexedObservationRangeCompHausLimitAction D α t x) =
          (compactIndexedObservationRangeCompHausLimitAction D α (t + s)) x := by
            simpa using hts.symm
      _ = (compactIndexedObservationRangeCompHausLimitAction D α (s + t)) x := by
            rw [add_comm]
      _ = (compactIndexedObservationRangeCompHausLimitAction D α t)
          (compactIndexedObservationRangeCompHausLimitAction D α s x) := by
            simpa using hst

theorem compactIndexedObservationRangeCompHausLimit_orbitClosure_mono
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    {x y : compactIndexedObservationRangeCompHausLimit D}
    (h : compactIndexedObservationRangeCompHausLimitOrbit D α x ⊆
      compactIndexedObservationRangeCompHausLimitOrbit D α y) :
    compactIndexedObservationRangeCompHausLimitOrbitClosure D α x ⊆
      compactIndexedObservationRangeCompHausLimitOrbitClosure D α y := by
  exact closure_mono h

noncomputable def compactIndexedObservationRangeCompHausLimitActionHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimit D ≃ₜ
      compactIndexedObservationRangeCompHausLimit D := by
  let e := compactIndexedObservationRangeCompHausLimitActionIso
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

theorem compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitActionHomeomorph
        D α hα0 hαadd s ''
        compactIndexedObservationRangeCompHausLimitOrbit D α x =
      compactIndexedObservationRangeCompHausLimitOrbit D α
        (compactIndexedObservationRangeCompHausLimitAction D α s x) := by
  change compactIndexedObservationRangeCompHausLimitAction D α s ''
      compactIndexedObservationRangeCompHausLimitOrbit D α x = _
  exact compactIndexedObservationRangeCompHausLimit_action_image_orbit
    D α hαadd s x

theorem compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitActionHomeomorph
        D α hα0 hαadd s ''
        compactIndexedObservationRangeCompHausLimitOrbitClosure D α x =
      compactIndexedObservationRangeCompHausLimitOrbitClosure D α
        (compactIndexedObservationRangeCompHausLimitAction D α s x) := by
  rw [compactIndexedObservationRangeCompHausLimitOrbitClosure,
    compactIndexedObservationRangeCompHausLimitOrbitClosure]
  rw [(compactIndexedObservationRangeCompHausLimitActionHomeomorph
    D α hα0 hαadd s).image_closure]
  exact congrArg closure
    (compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbit
      D α hα0 hαadd s x)

abbrev compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :=
  {y // y ∈ compactIndexedObservationRangeCompHausLimitOrbitClosure D α x}

noncomputable def compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) : CompHaus := by
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α x) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_orbitClosure D α x)
  exact CompHaus.of
    (compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α x)

noncomputable def compactIndexedObservationRangeCompHausLimitOrbitClosureFlowHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationRangeCompHausLimit D)
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α x ≃ₜ
      compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α
        (compactIndexedObservationRangeCompHausLimitAction D α t x) := by
  let h_orbit := compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbitClosure
    D α hα0 hαadd t x
  exact
    { toFun := fun y => ⟨
          compactIndexedObservationRangeCompHausLimitAction D α t y.1, by
          rw [← h_orbit]
          exact ⟨y.1, y.2, rfl⟩⟩
      invFun := fun y => ⟨
          compactIndexedObservationRangeCompHausLimitAction D α (-t) y.1, by
          have h := compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbitClosure
            D α hα0 hαadd (-t) (compactIndexedObservationRangeCompHausLimitAction D α t x)
          have hcancel := congrArg (fun f => f x)
            (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd t (-t))
          rw [add_neg_cancel,
            compactIndexedObservationRangeCompHausLimitAction_zero D α hα0] at hcancel
          have hx :
              compactIndexedObservationRangeCompHausLimitAction D α (-t)
                  (compactIndexedObservationRangeCompHausLimitAction D α t x) = x := by
            simpa using hcancel.symm
          rw [hx] at h
          rw [← h]
          exact ⟨y.1, y.2, rfl⟩⟩
      left_inv := by
        intro y
        apply Subtype.ext
        have h := congrArg (fun f => f y.1)
          (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd t (-t))
        rw [add_neg_cancel,
          compactIndexedObservationRangeCompHausLimitAction_zero D α hα0] at h
        simpa using h.symm
      right_inv := by
        intro y
        apply Subtype.ext
        have h := congrArg (fun f => f y.1)
          (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd (-t) t)
        rw [neg_add_cancel,
          compactIndexedObservationRangeCompHausLimitAction_zero D α hα0] at h
        simpa using h.symm
      continuous_toFun :=
        (compactIndexedObservationRangeCompHausLimitActionHomeomorph
          D α hα0 hαadd t).continuous_toFun.comp continuous_subtype_val |>.subtype_mk
            (fun y => by
              rw [← h_orbit]
              exact ⟨y.1, y.2, rfl⟩)
      continuous_invFun :=
        (compactIndexedObservationRangeCompHausLimitActionHomeomorph
          D α hα0 hαadd (-t)).continuous_toFun.comp continuous_subtype_val |>.subtype_mk
            (fun y => by
              have h := compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbitClosure
                D α hα0 hαadd (-t)
                  (compactIndexedObservationRangeCompHausLimitAction D α t x)
              have hcancel := congrArg (fun f => f x)
                (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd t (-t))
              rw [add_neg_cancel,
                compactIndexedObservationRangeCompHausLimitAction_zero D α hα0] at hcancel
              have hx :
                  compactIndexedObservationRangeCompHausLimitAction D α (-t)
                      (compactIndexedObservationRangeCompHausLimitAction D α t x) = x := by
                simpa using hcancel.symm
              rw [hx] at h
              rw [← h]
              exact ⟨y.1, y.2, rfl⟩) }

noncomputable def compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationRangeCompHausLimit D)
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α x ≅
      compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α
        (compactIndexedObservationRangeCompHausLimitAction D α t x) := by
  let e := compactIndexedObservationRangeCompHausLimitOrbitClosureFlowHomeomorph
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

theorem compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso_hom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationRangeCompHausLimit D)
    (t : ℝ)
    (y : compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α x) :
    (compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso
      D α hα0 hαadd x t).hom y =
      compactIndexedObservationRangeCompHausLimitOrbitClosureFlowHomeomorph
        D α hα0 hαadd x t y :=
  rfl

theorem compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso_comp_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationRangeCompHausLimit D)
    (s t : ℝ)
    (y : compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α x) :
    (((compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso
      D α hα0 hαadd x s).hom ≫
        (compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso
          D α hα0 hαadd
          (compactIndexedObservationRangeCompHausLimitAction D α s x) t).hom) y).1 =
      ((compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso
        D α hα0 hαadd x (t + s)).hom y).1 := by
  change
    (compactIndexedObservationRangeCompHausLimitAction D α t)
        ((compactIndexedObservationRangeCompHausLimitAction D α s) y.1) =
      (compactIndexedObservationRangeCompHausLimitAction D α (t + s)) y.1
  have h := congrArg (fun f => f y.1)
    (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s t)
  simpa [add_comm] using h.symm

theorem compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso_comp
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationRangeCompHausLimit D)
    (s t : ℝ) :
    let harg :
        compactIndexedObservationRangeCompHausLimitAction D α t
            (compactIndexedObservationRangeCompHausLimitAction D α s x) =
          compactIndexedObservationRangeCompHausLimitAction D α (t + s) x := by
      have h := congrArg (fun f => f x)
        (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s t)
      simpa [add_comm] using h.symm
    let hset := congrArg
      (fun z => compactIndexedObservationRangeCompHausLimitOrbitClosure D α z)
      harg
    let e :=
      (compactIndexedObservationRangeCompHausLimitOrbitClosureFlowHomeomorph
        D α hα0 hαadd x s).trans
        ((compactIndexedObservationRangeCompHausLimitOrbitClosureFlowHomeomorph
          D α hα0 hαadd
          (compactIndexedObservationRangeCompHausLimitAction D α s x) t).trans
          (Homeomorph.setCongr hset))
    (CompHausLike.isoOfHomeo e).hom =
      (compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso
        D α hα0 hαadd x (t + s)).hom := by
  dsimp
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  simpa [Category.assoc] using
    compactIndexedObservationRangeCompHausLimitOrbitClosureFlowIso_comp_apply
      D α hα0 hαadd x s t y

end InfoGeometry.Topology
