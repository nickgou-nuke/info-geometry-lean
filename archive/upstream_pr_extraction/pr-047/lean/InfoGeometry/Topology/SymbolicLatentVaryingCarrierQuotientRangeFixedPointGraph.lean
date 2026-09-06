import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeJointContinuity
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointsCompHaus
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeFixedPointsNaturality
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic

/-!
# Closed fixed-point graphs for varying symbolic carriers

Joint continuity makes the relation "the time slice at `t` fixes `x`" a
closed subset of `ℝ × carrier`.  Its fibers are exactly the fixed-point sets
used by the CompHaus owners.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationQuotientCompHausLimitFixedPointGraph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) : Set
      (ℝ × compactIndexedObservationQuotientCompHausLimit D) :=
  {p | compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2 = p.2}

def compactIndexedObservationRangeCompHausLimitFixedPointGraph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D)) : Set
      (ℝ × compactIndexedObservationRangeCompHausLimit D) :=
  {p | compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2 = p.2}

theorem compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointGraph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    IsClosed (compactIndexedObservationQuotientCompHausLimitFixedPointGraph D α) := by
  exact isClosed_eq hjoint continuous_snd

theorem compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointGraph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    IsClosed (compactIndexedObservationRangeCompHausLimitFixedPointGraph D α) := by
  exact isClosed_eq hjoint continuous_snd

theorem compactIndexedObservationQuotientCompHausLimit_fixedPointGraph_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    _root_.Topology.IsClosedEmbedding
      (Subtype.val :
        compactIndexedObservationQuotientCompHausLimitFixedPointGraph D α →
          ℝ × compactIndexedObservationQuotientCompHausLimit D) := by
  exact (compactIndexedObservationQuotientCompHausLimit_isClosed_fixedPointGraph
    D α hjoint).isClosedEmbedding_subtypeVal

theorem compactIndexedObservationRangeCompHausLimit_fixedPointGraph_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hjoint : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    _root_.Topology.IsClosedEmbedding
      (Subtype.val :
        compactIndexedObservationRangeCompHausLimitFixedPointGraph D α →
          ℝ × compactIndexedObservationRangeCompHausLimit D) := by
  exact (compactIndexedObservationRangeCompHausLimit_isClosed_fixedPointGraph
    D α hjoint).isClosedEmbedding_subtypeVal

@[simp] theorem compactIndexedObservationQuotientCompHausLimit_mem_fixedPointGraph_iff
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (t : ℝ)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    (t, x) ∈ compactIndexedObservationQuotientCompHausLimitFixedPointGraph D α ↔
      x ∈ compactIndexedObservationQuotientCompHausLimitFixedPointSet D α t :=
  Iff.rfl

@[simp] theorem compactIndexedObservationRangeCompHausLimit_mem_fixedPointGraph_iff
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (t : ℝ)
    (x : compactIndexedObservationRangeCompHausLimit D) :
    (t, x) ∈ compactIndexedObservationRangeCompHausLimitFixedPointGraph D α ↔
      x ∈ compactIndexedObservationRangeCompHausLimitFixedPointSet D α t :=
  Iff.rfl

noncomputable def compactIndexedObservationQuotientRangeFixedPointGraphHomeomorph
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι) :
    (ℝ × compactIndexedObservationQuotientCompHausLimit D) ≃ₜ
      (ℝ × compactIndexedObservationRangeCompHausLimit D) := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
  refine
    { toFun := fun p => (p.1, e p.2)
      invFun := fun p => (p.1, e.symm p.2)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro p
    rcases p with ⟨t, x⟩
    simp
  · intro p
    rcases p with ⟨t, x⟩
    simp
  · exact continuous_fst.prodMk (e.continuous.comp continuous_snd)
  · exact continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)

theorem compactIndexedObservationQuotientRangeFixedPointGraph_image
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t) :
    (fun p : ℝ × compactIndexedObservationQuotientCompHausLimit D =>
      (p.1, compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D p.2)) ''
        compactIndexedObservationQuotientCompHausLimitFixedPointGraph D α =
      compactIndexedObservationRangeCompHausLimitFixedPointGraph D α := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨t, x⟩
    change compactIndexedObservationRangeCompHausLimitAction D α t
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) =
      compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd t x
    rw [← h]
    exact congrArg (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D) hq
  · intro hp
    refine ⟨(p.1,
      (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2), ?_, ?_⟩
    · change compactIndexedObservationQuotientCompHausLimitAction D α p.1
        ((compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2) =
      (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2
      apply (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).injective
      have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
        D α hα0 hαadd p.1
          ((compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2)
      calc
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D)
            (compactIndexedObservationQuotientCompHausLimitAction D α p.1
              ((compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2)) =
            compactIndexedObservationRangeCompHausLimitAction D α p.1
              ((compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D)
                ((compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2)) := h
        _ = compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2 := by
          rw [(compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).apply_symm_apply]
        _ = p.2 := hp
        _ = (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D)
            ((compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).symm p.2) := by
          rw [(compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).apply_symm_apply]
    · simp

theorem compactIndexedObservationQuotientRangeFixedPointGraphHomeomorph_image
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t) :
    compactIndexedObservationQuotientRangeFixedPointGraphHomeomorph
      D ''
        compactIndexedObservationQuotientCompHausLimitFixedPointGraph D α =
      compactIndexedObservationRangeCompHausLimitFixedPointGraph D α := by
  simpa [compactIndexedObservationQuotientRangeFixedPointGraphHomeomorph] using
    compactIndexedObservationQuotientRangeFixedPointGraph_image D α hα0 hαadd

end InfoGeometry.Topology
