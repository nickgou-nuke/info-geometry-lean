import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Solution fibers as topological subobjects

Finite symbolic systems already provide closed solution sets.  This owner
packages each solution fiber as its native subtype and exposes the canonical
inclusion in `TopCat`.
-/

abbrev symbolicLatentSolutionFiber
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :=
  {x // x ∈ S.solutionSet values}

def symbolicLatentSolutionFiberInclusion
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    TopCat.of (symbolicLatentSolutionFiber S values) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := (Subtype.val : symbolicLatentSolutionFiber S values → X)
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentSolutionFiberInclusion_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (x : symbolicLatentSolutionFiber S values) :
    symbolicLatentSolutionFiberInclusion S values x = x.1 :=
  rfl

theorem symbolicLatentSolutionFiber_isClosedEmbedding
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    Topology.IsClosedEmbedding
      (Subtype.val : symbolicLatentSolutionFiber S values → X) := by
  exact (isClosed_finiteSymbolicLatentSystem_solutionSet S values).isClosedEmbedding_subtypeVal

theorem isCompact_symbolicLatentSolutionFiber
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    IsCompact ((Subtype.val : symbolicLatentSolutionFiber S values → X) ''
      (Set.univ : Set (symbolicLatentSolutionFiber S values))) := by
  simpa only [Set.image_univ, Subtype.range_val] using
    (isClosed_finiteSymbolicLatentSystem_solutionSet S values).isCompact

theorem symbolicLatentSolutionFiber_mem_iff_observation
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (x : X) :
    x ∈ S.solutionSet values ↔
      symbolicObservationMap S x = values := by
  constructor
  · intro hx
    funext i
    exact hx i
  · intro hx i
    exact congrFun hx i

def symbolicLatentSolutionFiberMap
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    symbolicLatentSolutionFiber S values →
      symbolicLatentSolutionFiber T values :=
  fun x => ⟨F.toFun x, F.map_solutionSet values ⟨x, x.property, rfl⟩⟩

theorem continuous_symbolicLatentSolutionFiberMap
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    Continuous (symbolicLatentSolutionFiberMap F values) := by
  exact (F.continuous_toFun.comp continuous_subtype_val).subtype_mk
    (fun x => F.map_solutionSet values ⟨x, x.property, rfl⟩)

def symbolicLatentSolutionFiberTopCatHom
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    TopCat.of (symbolicLatentSolutionFiber S values) ⟶
      TopCat.of (symbolicLatentSolutionFiber T values) :=
  TopCat.ofHom
    { toFun := symbolicLatentSolutionFiberMap F values
      continuous_toFun := continuous_symbolicLatentSolutionFiberMap F values }

theorem symbolicLatentSolutionFiberTopCatHom_id
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    symbolicLatentSolutionFiberTopCatHom
        (SymbolicLatentMorphism.id S) values =
      𝟙 (TopCat.of (symbolicLatentSolutionFiber S values)) := by
  ext x
  rfl

theorem symbolicLatentSolutionFiberTopCatHom_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    symbolicLatentSolutionFiberTopCatHom
        (SymbolicLatentMorphism.comp g f) values =
      symbolicLatentSolutionFiberTopCatHom f values ≫
        symbolicLatentSolutionFiberTopCatHom g values := by
  ext x
  rfl

end InfoGeometry.Topology
