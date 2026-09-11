import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeFunctor

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type} [Fintype ι]

/-- The compact Hausdorff map induced on symbolic-latent feasible subspaces by
    a morphism of latent systems. -/
noncomputable def symbolicLatentFeasibleSubspaceCompHausHom
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentFeasibleSubspaceCompHaus S targets hclosed ⟶
      symbolicLatentFeasibleSubspaceCompHaus T targets hclosed := by
  exact ⟨TopCat.ofHom
    { toFun := F.feasibleSubspaceMap targets
      continuous_toFun := F.continuous_feasibleSubspaceMap targets }⟩

/-- Forgetting the compact Hausdorff structure recovers the native topological
    feasible-subspace map. -/
theorem symbolicLatentFeasibleSubspaceCompHausHom_forget
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    compHausToTop.map (symbolicLatentFeasibleSubspaceCompHausHom F targets hclosed) =
      symbolicLatentFeasibleSubspaceTopCatHom F targets := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

theorem symbolicLatentFeasibleSubspaceCompHausHom_id
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentFeasibleSubspaceCompHausHom
        (SymbolicLatentMorphism.id S) targets hclosed =
      𝟙 (symbolicLatentFeasibleSubspaceCompHaus S targets hclosed) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem symbolicLatentFeasibleSubspaceCompHausHom_comp
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    symbolicLatentFeasibleSubspaceCompHausHom
        (SymbolicLatentMorphism.comp g f) targets hclosed =
      symbolicLatentFeasibleSubspaceCompHausHom f targets hclosed ≫
        symbolicLatentFeasibleSubspaceCompHausHom g targets hclosed := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The feasible-subspace lift packages as a genuine `CompHaus` functor. -/
noncomputable def symbolicLatentFeasibleSubspaceCompHausFunctor
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    (FiniteSymbolicLatentSystem X ι) ⥤ CompHaus where
  obj S := symbolicLatentFeasibleSubspaceCompHaus S targets hclosed
  map F := symbolicLatentFeasibleSubspaceCompHausHom F targets hclosed
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp g f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
