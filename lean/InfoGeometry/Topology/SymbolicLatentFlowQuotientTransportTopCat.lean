import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentFlowQuotientTransport

namespace InfoGeometry.Topology

open CategoryTheory
noncomputable section

/-!
# TopCat packaging of the finite symbolic latent quotient flow

The preceding owner constructs the flow on the observational quotient and on
its closed image.  This file records the same action as an invertible `TopCat`
morphism; it adds no analytic or KMS interpretation.
-/

def rangeFlowTopCatHom
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    TopCat.of (Set.range (symbolicObservationQuotientMap S)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap S)) :=
  TopCat.ofHom
    { toFun := rangeFlowHomeomorph F t
      continuous_toFun := (rangeFlowHomeomorph F t).continuous }

@[simp] theorem rangeFlowTopCatHom_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowTopCatHom F t y = rangeFlowAct F t y :=
  rfl

theorem rangeFlowTopCatHom_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) :
    rangeFlowTopCatHom F 0 = 𝟙
      (TopCat.of (Set.range (symbolicObservationQuotientMap S))) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  change rangeFlowAct F 0 y = y
  exact rangeFlowAct_zero F y

theorem rangeFlowTopCatHom_add
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s t : ℝ) :
    rangeFlowTopCatHom F (s + t) =
      rangeFlowTopCatHom F s ≫ rangeFlowTopCatHom F t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  simpa [rangeFlowTopCatHom, CategoryTheory.comp_apply, add_comm] using
    rangeFlowAct_add F t s y

theorem rangeFlowTopCatHom_comp
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t s : ℝ) :
    rangeFlowTopCatHom F t ≫ rangeFlowTopCatHom F s =
      rangeFlowTopCatHom F (t + s) := by
  simpa using (rangeFlowTopCatHom_add F t s).symm

@[simp] theorem rangeFlowTopCatHom_comp_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t s : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    (rangeFlowTopCatHom F t ≫ rangeFlowTopCatHom F s) y =
      rangeFlowTopCatHom F (t + s) y := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun f => f y) (rangeFlowTopCatHom_comp F t s)

theorem rangeFlowTopCatHom_isIso
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    IsIso (rangeFlowTopCatHom F t) := by
  refine IsIso.mk ⟨
    TopCat.ofHom
      { toFun := (rangeFlowHomeomorph F t).symm
        continuous_toFun := (rangeFlowHomeomorph F t).symm.continuous }, ?_, ?_⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change (rangeFlowHomeomorph F t).symm (rangeFlowAct F t y) = y
    exact (rangeFlowHomeomorph F t).symm_apply_apply y
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change rangeFlowAct F t ((rangeFlowHomeomorph F t).symm y) = y
    exact (rangeFlowHomeomorph F t).apply_symm_apply y

end
end InfoGeometry.Topology
