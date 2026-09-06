import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitAction

/-!
# Fixed-point loci for varying-carrier inverse-limit actions

For a fixed time, the fixed points of the quotient or observation-range limit
action are equalizers of a continuous endomorphism and the identity.  They
are therefore closed compact Hausdorff subspaces of the native `CompHaus`
limits.  The final theorem records invariance of these loci under every
commuting time slice.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationQuotientCompHausLimitFixedPointSet
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    Set (compactIndexedObservationQuotientCompHausLimit D) :=
  {x | compactIndexedObservationQuotientCompHausLimitAction D α t x = x}

theorem compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointSet
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    IsClosed (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) := by
  exact isClosed_eq
    (compactIndexedObservationQuotientCompHausLimitAction D α t).hom.hom'.continuous
    continuous_id

theorem compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    IsCompact (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointSet D α t)
    (Set.subset_univ _)

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) : CompHaus := by
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet D α t)
  exact CompHaus.of
    (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t)

noncomputable def compactIndexedObservationQuotientCompHausLimitFixedPointInclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    compactIndexedObservationQuotientCompHausLimitFixedPointCompHaus D α t ⟶
      compactIndexedObservationQuotientCompHausLimit D := by
  letI : CompactSpace
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationQuotientCompHausLimit_isCompact_fixedPointSet D α t)
  change CompHaus.of
      (compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) ⟶
    compactIndexedObservationQuotientCompHausLimit D
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

@[simp] theorem compactIndexedObservationQuotientCompHausLimitFixedPointInclusion_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationQuotientCompHausLimitFixedPointInclusion D α t x = x.1 :=
  rfl

theorem compactIndexedObservationQuotientCompHausLimit_fixedPointSet_invariant
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t s : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (hx : x ∈ compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationQuotientCompHausLimitAction D α s x ∈
      compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t := by
  change compactIndexedObservationQuotientCompHausLimitAction D α t
      (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
    compactIndexedObservationQuotientCompHausLimitAction D α s x
  calc
    compactIndexedObservationQuotientCompHausLimitAction D α t
        (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
        compactIndexedObservationQuotientCompHausLimitAction D α (s + t) x := by
      have h := congrArg (fun f => f x)
        (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s t)
      simpa [add_comm] using h.symm
    _ = compactIndexedObservationQuotientCompHausLimitAction D α (t + s) x := by
      rw [add_comm]
    _ = compactIndexedObservationQuotientCompHausLimitAction D α s
        (compactIndexedObservationQuotientCompHausLimitAction D α t x) := by
      have h := congrArg (fun f => f x)
        (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd t s)
      simpa using h
    _ = compactIndexedObservationQuotientCompHausLimitAction D α s x := by
      rw [show compactIndexedObservationQuotientCompHausLimitAction D α t x = x by
        exact hx]

def compactIndexedObservationRangeCompHausLimitFixedPointSet
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    Set (compactIndexedObservationRangeCompHausLimit D) :=
  {x | compactIndexedObservationRangeCompHausLimitAction D α t x = x}

theorem compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointSet
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    IsClosed (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) := by
  exact isClosed_eq
    (compactIndexedObservationRangeCompHausLimitAction D α t).hom.hom'.continuous
    continuous_id

theorem compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    IsCompact (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointSet D α t)
    (Set.subset_univ _)

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointCompHaus
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) : CompHaus := by
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet D α t)
  exact CompHaus.of
    (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t)

noncomputable def compactIndexedObservationRangeCompHausLimitFixedPointInclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ) :
    compactIndexedObservationRangeCompHausLimitFixedPointCompHaus D α t ⟶
      compactIndexedObservationRangeCompHausLimit D := by
  letI : CompactSpace
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :=
    isCompact_iff_compactSpace.mp
      (compactIndexedObservationRangeCompHausLimit_isCompact_fixedPointSet D α t)
  change CompHaus.of
      (compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) ⟶
    compactIndexedObservationRangeCompHausLimit D
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

@[simp] theorem compactIndexedObservationRangeCompHausLimitFixedPointInclusion_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) (t : ℝ)
    (x : compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationRangeCompHausLimitFixedPointInclusion D α t x = x.1 :=
  rfl

theorem compactIndexedObservationRangeCompHausLimit_fixedPointSet_invariant
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (t s : ℝ)
    (x : compactIndexedObservationRangeCompHausLimit D)
    (hx : x ∈ compactIndexedObservationRangeCompHausLimitFixedPointSet D α t) :
    compactIndexedObservationRangeCompHausLimitAction D α s x ∈
      compactIndexedObservationRangeCompHausLimitFixedPointSet D α t := by
  change compactIndexedObservationRangeCompHausLimitAction D α t
      (compactIndexedObservationRangeCompHausLimitAction D α s x) =
    compactIndexedObservationRangeCompHausLimitAction D α s x
  calc
    compactIndexedObservationRangeCompHausLimitAction D α t
        (compactIndexedObservationRangeCompHausLimitAction D α s x) =
        compactIndexedObservationRangeCompHausLimitAction D α (s + t) x := by
      have h := congrArg (fun f => f x)
        (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s t)
      simpa [add_comm] using h.symm
    _ = compactIndexedObservationRangeCompHausLimitAction D α (t + s) x := by
      rw [add_comm]
    _ = compactIndexedObservationRangeCompHausLimitAction D α s
        (compactIndexedObservationRangeCompHausLimitAction D α t x) := by
      have h := congrArg (fun f => f x)
        (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd t s)
      simpa using h
    _ = compactIndexedObservationRangeCompHausLimitAction D α s x := by
      rw [show compactIndexedObservationRangeCompHausLimitAction D α t x = x by
        exact hx]

end InfoGeometry.Topology
