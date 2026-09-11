import Mathlib.Topology.Category.CompHaus.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentSolutionFeasibleIncidenceTopCat
import InfoGeometry.Topology.SymbolicLatentSolutionFiberCompHaus
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHaus
import InfoGeometry.Topology.SymbolicLatentSolutionFiberCompHausFlow
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHausFlow

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def symbolicLatentSolutionFiberToFeasibleCompHausHom
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentSolutionFiberCompHaus S values ⟶
      symbolicLatentFeasibleSubspaceCompHaus S targets hclosed := by
  exact ⟨TopCat.ofHom
    { toFun := symbolicLatentSolutionFiberToFeasible
        S values targets hvalues
      continuous_toFun := continuous_symbolicLatentSolutionFiberToFeasible
        S values targets hvalues }⟩

@[simp] theorem symbolicLatentSolutionFiberToFeasibleCompHausHom_apply
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (hclosed : ∀ i, IsClosed (targets i))
    (x : symbolicLatentSolutionFiber S values) :
    symbolicLatentSolutionFiberToFeasibleCompHausHom
        S values targets hvalues hclosed x =
      symbolicLatentSolutionFiberToFeasible S values targets hvalues x :=
  rfl

theorem symbolicLatentSolutionFiberToFeasibleCompHausHom_forget
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (hclosed : ∀ i, IsClosed (targets i)) :
    compHausToTop.map
        (symbolicLatentSolutionFiberToFeasibleCompHausHom
          S values targets hvalues hclosed) =
      symbolicLatentSolutionFiberToFeasibleTopCatHom
        S values targets hvalues := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

noncomputable def symbolicLatentSolutionFiberCompHausInclusion
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    symbolicLatentSolutionFiberCompHaus S values ⟶ CompHaus.of X := by
  exact ⟨TopCat.ofHom
    { toFun := (Subtype.val : symbolicLatentSolutionFiber S values → X)
      continuous_toFun := continuous_subtype_val }⟩

noncomputable def symbolicLatentFeasibleSubspaceCompHausInclusion
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentFeasibleSubspaceCompHaus S targets hclosed ⟶ CompHaus.of X := by
  exact ⟨TopCat.ofHom
    { toFun := (Subtype.val : feasibleLatentSubspace S targets → X)
      continuous_toFun := continuous_subtype_val }⟩

theorem symbolicLatentSolutionFiberToFeasibleCompHausHom_factorization
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentSolutionFiberToFeasibleCompHausHom
        S values targets hvalues hclosed ≫
        symbolicLatentFeasibleSubspaceCompHausInclusion S targets hclosed =
      symbolicLatentSolutionFiberCompHausInclusion S values := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

noncomputable def symbolicLatentSolutionFiberCompHausHomOfMorphism
    {X Y ι : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    symbolicLatentSolutionFiberCompHaus S values ⟶
      symbolicLatentSolutionFiberCompHaus T values := by
  exact ⟨TopCat.ofHom
    { toFun := symbolicLatentSolutionFiberMap F values
      continuous_toFun := continuous_symbolicLatentSolutionFiberMap F values }⟩

noncomputable def symbolicLatentFeasibleSubspaceCompHausHomOfMorphism
    {X Y ι : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentFeasibleSubspaceCompHaus S targets hclosed ⟶
      symbolicLatentFeasibleSubspaceCompHaus T targets hclosed := by
  exact ⟨TopCat.ofHom
    { toFun := F.feasibleSubspaceMap targets
      continuous_toFun := F.continuous_feasibleSubspaceMap targets }⟩

theorem symbolicLatentSolutionFiberFeasibleCompHaus_naturality
    {X Y ι : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentSolutionFiberToFeasibleCompHausHom
        S values targets hvalues hclosed ≫
        symbolicLatentFeasibleSubspaceCompHausHomOfMorphism F targets hclosed =
      symbolicLatentSolutionFiberCompHausHomOfMorphism F values ≫
        symbolicLatentSolutionFiberToFeasibleCompHausHom
          T values targets hvalues hclosed := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem SymbolicLatentFlow.solutionFiberFeasibleCompHaus_flow_naturality
    {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (hclosed : ∀ i, IsClosed (targets i)) (t : ℝ) :
    symbolicLatentSolutionFiberToFeasibleCompHausHom
        S values targets hvalues hclosed ≫
        (symbolicLatentFeasibleSubspaceCompHausFlowIso
          F targets hclosed t).hom =
      (F.solutionFiberCompHausFlowIso values t).hom ≫
        symbolicLatentSolutionFiberToFeasibleCompHausHom
          S values targets hvalues hclosed := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end
end InfoGeometry.Topology
