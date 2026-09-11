import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ContinuousModularFlowQuotientDescent

namespace InfoGeometry.Topology.ContinuousQuotientDescent

open CategoryTheory

/-- The descended modular flow as a `TopCat` endomorphism on the quotient space. -/
noncomputable def descendedModularFlowTopCatHom
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) :
    TopCat.of Q ⟶ TopCat.of Q :=
  TopCat.ofHom
    { toFun := descended q t
      continuous_toFun := continuous_descended q t }

@[simp] theorem descendedModularFlowTopCatHom_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) (y : Q) :
    descendedModularFlowTopCatHom q t y = descended q t y :=
  rfl

theorem descendedModularFlowTopCatHom_zero
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) :
    descendedModularFlowTopCatHom q 0 = 𝟙 (TopCat.of Q) := by
  ext y
  exact descended_zero q y

theorem descendedModularFlowTopCatHom_add
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (s t : ℤ) :
    descendedModularFlowTopCatHom q (s + t) =
      descendedModularFlowTopCatHom q s ≫
        descendedModularFlowTopCatHom q t := by
  ext y
  change descended q (s + t) y = descended q t (descended q s y)
  simpa [add_comm] using descended_add q t s y

@[simp] theorem descendedModularFlowTopCatHom_add_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (s t : ℤ) (y : Q) :
    descendedModularFlowTopCatHom q (s + t) y =
      descendedModularFlowTopCatHom q t
        (descendedModularFlowTopCatHom q s y) := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun f => f y) (descendedModularFlowTopCatHom_add q s t)

theorem descendedModularFlowTopCatHom_isIso
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) :
    IsIso (descendedModularFlowTopCatHom q t) := by
  refine IsIso.mk ⟨TopCat.ofHom
    { toFun := descended q (-t)
      continuous_toFun := continuous_descended q (-t) }, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext y
    change descended q (-t) (descended q t y) = y
    rw [← descended_add q (-t) t y]
    simpa [add_comm] using descended_zero q y
  · apply TopCat.hom_ext
    ext y
    change descended q t (descended q (-t) y) = y
    rw [← descended_add q t (-t) y]
    simpa using descended_zero q y

end InfoGeometry.Topology.ContinuousQuotientDescent
