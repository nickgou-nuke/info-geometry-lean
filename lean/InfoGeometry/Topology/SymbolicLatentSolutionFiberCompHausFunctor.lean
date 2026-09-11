import InfoGeometry.Topology.SymbolicLatentSolutionFiberCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeFunctor

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type} [Fintype ι]

/-- The compact Hausdorff solution-fiber lift induced by a symbolic latent morphism. -/
noncomputable def symbolicLatentSolutionFiberCompHausHom
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (values : ι → ℝ) :
    symbolicLatentSolutionFiberCompHaus S values ⟶
      symbolicLatentSolutionFiberCompHaus T values := by
  exact ⟨TopCat.ofHom
    { toFun := symbolicLatentSolutionFiberMap F values
      continuous_toFun := continuous_symbolicLatentSolutionFiberMap F values }⟩

/-- Forgetting the compact Hausdorff structure recovers the native topological map. -/
theorem symbolicLatentSolutionFiberCompHausHom_forget
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (values : ι → ℝ) :
    compHausToTop.map (symbolicLatentSolutionFiberCompHausHom F values) =
      symbolicLatentSolutionFiberTopCatHom F values := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

theorem symbolicLatentSolutionFiberCompHausHom_id
    (S : FiniteSymbolicLatentSystem X ι)
    (values : ι → ℝ) :
    symbolicLatentSolutionFiberCompHausHom
        (SymbolicLatentMorphism.id S) values =
      𝟙 (symbolicLatentSolutionFiberCompHaus S values) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem symbolicLatentSolutionFiberCompHausHom_comp
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : T ⟶ U)
    (f : S ⟶ T)
    (values : ι → ℝ) :
    symbolicLatentSolutionFiberCompHausHom
        (SymbolicLatentMorphism.comp g f) values =
      symbolicLatentSolutionFiberCompHausHom f values ≫
        symbolicLatentSolutionFiberCompHausHom g values := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The solution-fiber lift packages as a genuine `CompHaus` functor. -/
noncomputable def symbolicLatentSolutionFiberCompHausFunctor
    (values : ι → ℝ) :
    (FiniteSymbolicLatentSystem X ι) ⥤ CompHaus where
  obj S := symbolicLatentSolutionFiberCompHaus S values
  map F := symbolicLatentSolutionFiberCompHausHom F values
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp := by
    intro S T U f g
    simpa using
      (symbolicLatentSolutionFiberCompHausHom_comp (S := S) (T := T) (U := U)
        (g := g) (f := f) values)

end
end InfoGeometry.Topology
