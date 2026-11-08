import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeOrbitClosureNaturality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# CompHaus naturality of quotient-range orbit closures

The ambient quotient-range homeomorphism restricts to the orbit closures.
This file packages that restriction as a genuine `CompHaus` isomorphism and
proves its compatibility with the restricted flows.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitOrbitClosureCompHaus D α x ⟶
      compactIndexedObservationQuotientCompHausLimit D := by
  exact ⟨TopCat.ofHom
    { toFun := fun y => y.1
      continuous_toFun := continuous_subtype_val }⟩

noncomputable def compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α x ⟶
      compactIndexedObservationRangeCompHausLimit D := by
  exact ⟨TopCat.ofHom
    { toFun := fun y => y.1
      continuous_toFun := continuous_subtype_val }⟩

theorem compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    Topology.IsClosedEmbedding
      (fun y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier
        D α x => y.1) := by
  exact (compactIndexedObservationQuotientCompHausLimit_isClosed_orbitClosure
    D α x).isClosedEmbedding_subtypeVal

theorem compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion_injective
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    Function.Injective
      (fun y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier
        D α x => y.1) := by
  exact (compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion_isClosedEmbedding
    D α x).injective

theorem compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :
    Topology.IsClosedEmbedding
      (fun y : compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier
        D α x => y.1) := by
  exact (compactIndexedObservationRangeCompHausLimit_isClosed_orbitClosure
    D α x).isClosedEmbedding_subtypeVal

theorem compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion_injective
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationRangeCompHausLimit D) :
    Function.Injective
      (fun y : compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier
        D α x => y.1) := by
  exact (compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion_isClosedEmbedding
    D α x).injective

theorem compactIndexedObservationQuotientRangeOrbitClosureHomeomorph_isClosedEmbedding_on_subtype
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    Topology.IsClosedEmbedding
      (fun y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x =>
        compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D y.1) := by
  exact (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D).isClosedEmbedding.comp
    (compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion_isClosedEmbedding
      D α x)

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_transport_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    Topology.IsClosedEmbedding
      (fun y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier
        D α x =>
        (compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
          D α hα0 hαadd x y).1) := by
  exact (compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion_isClosedEmbedding
    D α (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x)).comp
      (compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
        D α hα0 hαadd x).isClosedEmbedding

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_transport_inverse_isClosedEmbedding
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    Topology.IsClosedEmbedding
      (fun y : compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier
        D α (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) =>
        (compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
          D α hα0 hαadd x).symm y |>.1) := by
  exact (compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion_isClosedEmbedding
    D α x).comp
      (compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
        D α hα0 hαadd x).symm.isClosedEmbedding

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_inclusion_naturality_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (y : compactIndexedObservationQuotientCompHausLimitOrbitClosureCarrier D α x) :
    (compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion
      D α (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x)
      (compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
        D α hα0 hαadd x y)) =
      (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom
        (compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion
          D α x y) := by
  change
    compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
      D α hα0 hαadd x y =
      (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom y.1
  rfl

noncomputable def compactIndexedObservationQuotientRangeOrbitClosureCompHausIso
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitOrbitClosureCompHaus D α x ≅
    compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) := by
  let e := compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
    D α hα0 hαadd x
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

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_inclusion_naturality
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    (compactIndexedObservationQuotientRangeOrbitClosureCompHausIso
      D α hα0 hαadd x).hom ≫
        compactIndexedObservationRangeCompHausLimitOrbitClosureInclusion
          D α
          (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) =
      compactIndexedObservationQuotientCompHausLimitOrbitClosureInclusion
        D α x ≫
        (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom := by
  apply ConcreteCategory.hom_ext
  intro y
  change
    compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
      D α hα0 hαadd x y =
      (compactIndexedObservationQuotientRangeCompHausLimitIso D).hom y.1
  rfl

@[simp] theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_hom_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (y : compactIndexedObservationQuotientRangeOrbitClosureCarrier D α x) :
    (compactIndexedObservationQuotientRangeOrbitClosureCompHausIso
      D α hα0 hαadd x).hom y =
      compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
        D α hα0 hαadd x y := by
  rfl

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_action_apply
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (t : ℝ)
    (y : compactIndexedObservationQuotientRangeOrbitClosureCarrier D α x) :
    ((compactIndexedObservationRangeCompHausLimitOrbitClosureFlowHomeomorph
      D α hα0 hαadd
      (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x) t)
      ((compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
        D α hα0 hαadd x) y)).1 =
      ((compactIndexedObservationQuotientRangeOrbitClosureHomeomorph
        D α hα0 hαadd
        (compactIndexedObservationQuotientCompHausLimitAction D α t x))
        ((compactIndexedObservationQuotientCompHausLimitOrbitClosureFlowHomeomorph
          D α hα0 hαadd x t) y)).1 := by
  change
    compactIndexedObservationRangeCompHausLimitAction D α t
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D y.1) =
      compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
        (compactIndexedObservationQuotientCompHausLimitAction D α t y.1)
  exact (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
    D α hα0 hαadd t y.1).symm

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_action_carrier_eq
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
          (compactIndexedObservationQuotientCompHausLimitAction D α t x)) =
      compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α
        (compactIndexedObservationRangeCompHausLimitAction D α t
          (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x)) := by
  exact congrArg
    (fun z => compactIndexedObservationRangeCompHausLimitOrbitClosureCompHaus D α z)
    (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd t x)

theorem compactIndexedObservationQuotientRangeOrbitClosureCompHausIso_action_carrier_type_eq
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (x : compactIndexedObservationQuotientCompHausLimit D)
    (t : ℝ) :
    compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α
        (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
          (compactIndexedObservationQuotientCompHausLimitAction D α t x)) =
      compactIndexedObservationRangeCompHausLimitOrbitClosureCarrier D α
        (compactIndexedObservationRangeCompHausLimitAction D α t
          (compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D x)) := by
  congr 1
  exact compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
    D α hα0 hαadd t x

end InfoGeometry.Topology
