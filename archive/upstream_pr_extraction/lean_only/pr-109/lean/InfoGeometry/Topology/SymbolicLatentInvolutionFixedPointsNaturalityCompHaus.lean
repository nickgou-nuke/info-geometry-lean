import Mathlib.Topology.Category.CompHaus.Basic
import InfoGeometry.Topology.SymbolicLatentInvolutionFixedPointsCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def SymbolicLatentInvolution.fixedPointMapCompHausHom
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (f : X → Y) (hf : Continuous f)
    (hcomm : ∀ x, f (JX x) = JY (f x)) :
    symbolicLatentInvolutionFixedPointCompHaus JX ⟶
      symbolicLatentInvolutionFixedPointCompHaus JY := by
  exact ⟨TopCat.ofHom
    { toFun := fun x =>
        ⟨f x, by
          rw [mem_symbolicLatentInvolutionFixedPointSet]
          rw [← hcomm x, x.2]⟩
      continuous_toFun :=
        (hf.comp continuous_subtype_val).subtype_mk (fun x => by
          change JY (f (x : X)) = f (x : X)
          rw [← hcomm (x : X), x.2]) }⟩

@[simp] theorem SymbolicLatentInvolution.fixedPointMapCompHausHom_apply
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (f : X → Y) (hf : Continuous f)
    (hcomm : ∀ x, f (JX x) = JY (f x))
    (x : symbolicLatentInvolutionFixedPointSet JX) :
    JX.fixedPointMapCompHausHom JY f hf hcomm x =
      ⟨f x, by
        rw [mem_symbolicLatentInvolutionFixedPointSet]
        rw [← hcomm x, x.2]⟩ :=
  rfl

theorem SymbolicLatentInvolution.fixedPointMapCompHausHom_forget
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (f : X → Y) (hf : Continuous f)
    (hcomm : ∀ x, f (JX x) = JY (f x)) :
    compHausToTop.map (JX.fixedPointMapCompHausHom JY f hf hcomm) =
      TopCat.ofHom
        { toFun := fun x => by
            refine ⟨f (x : X), ?_⟩
            change JY (f (x : X)) = f (x : X)
            rw [← hcomm (x : X), x.2]
          continuous_toFun := by
            exact (hf.comp continuous_subtype_val).subtype_mk (fun x => by
              change JY (f (x : X)) = f (x : X)
              rw [← hcomm (x : X), x.2]) } := by
  rfl

theorem SymbolicLatentInvolution.fixedPointMapCompHausHom_naturality
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (f : X → Y) (hf : Continuous f)
    (hcomm : ∀ x, f (JX x) = JY (f x)) :
    JX.fixedPointMapCompHausHom JY f hf hcomm ≫
        JY.fixedPointInclusionCompHausHom =
      JX.fixedPointInclusionCompHausHom ≫
        (⟨TopCat.ofHom
          { toFun := f
            continuous_toFun := hf }⟩ : CompHaus.of X ⟶ CompHaus.of Y) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem SymbolicLatentInvolution.fixedPointMapCompHausHom_comp
    {X Y Z : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (JZ : SymbolicLatentInvolution Z)
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (hcomm_f : ∀ x, f (JX x) = JY (f x))
    (hcomm_g : ∀ y, g (JY y) = JZ (g y)) :
    JX.fixedPointMapCompHausHom JZ (g ∘ f) (hg.comp hf)
        (fun x => by
          simp only [Function.comp_apply]
          rw [hcomm_f, hcomm_g]) =
      JX.fixedPointMapCompHausHom JY f hf hcomm_f ≫
        JY.fixedPointMapCompHausHom JZ g hg hcomm_g := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

noncomputable def SymbolicLatentInvolution.fixedPointHomeomorphCompHausIso
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (e : X ≃ₜ Y)
    (hcomm : ∀ x, e (JX x) = JY (e x)) :
    symbolicLatentInvolutionFixedPointCompHaus JX ≅
      symbolicLatentInvolutionFixedPointCompHaus JY := by
  have hcomm_symm : ∀ y, e.symm (JY y) = JX (e.symm y) := by
    intro y
    apply e.injective
    simpa only [e.apply_symm_apply] using (hcomm (e.symm y)).symm
  let f := JX.fixedPointMapCompHausHom JY e e.continuous hcomm
  let g := JY.fixedPointMapCompHausHom JX e.symm e.symm.continuous hcomm_symm
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y.1 }

@[simp] theorem SymbolicLatentInvolution.fixedPointHomeomorphCompHausIso_hom_apply
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (e : X ≃ₜ Y)
    (hcomm : ∀ x, e (JX x) = JY (e x))
    (x : symbolicLatentInvolutionFixedPointSet JX) :
    (JX.fixedPointHomeomorphCompHausIso JY e hcomm).hom x =
      ⟨e x, by
        rw [mem_symbolicLatentInvolutionFixedPointSet]
        rw [← hcomm x, x.2]⟩ :=
  rfl

@[simp] theorem SymbolicLatentInvolution.fixedPointHomeomorphCompHausIso_inv_apply
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (JX : SymbolicLatentInvolution X)
    (JY : SymbolicLatentInvolution Y)
    (e : X ≃ₜ Y)
    (hcomm : ∀ x, e (JX x) = JY (e x))
    (y : symbolicLatentInvolutionFixedPointSet JY) :
    (JX.fixedPointHomeomorphCompHausIso JY e hcomm).inv y =
      ⟨e.symm y, by
        change JX (e.symm (y : Y)) = e.symm (y : Y)
        apply e.injective
        rw [hcomm, e.apply_symm_apply]
        exact y.2⟩ :=
  rfl

end
end InfoGeometry.Topology
