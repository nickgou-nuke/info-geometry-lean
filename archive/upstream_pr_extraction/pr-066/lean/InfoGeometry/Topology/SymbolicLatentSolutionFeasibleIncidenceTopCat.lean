import Mathlib
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat
import InfoGeometry.Topology.SymbolicLatentSolutionFiberTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
Incidence between exact symbolic-latent solution fibers and feasible
subspaces.  The only input beyond the native finite observable system is the
pointwise fact that the selected solution values lie in the target sets.
-/

def symbolicLatentSolutionFiberToFeasible
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i) :
    symbolicLatentSolutionFiber S values →
      feasibleLatentSubspace S targets :=
  fun x =>
    ⟨x.1, fun i => by
      rw [show (S.observable i) x.1 = values i by exact x.2 i]
      exact hvalues i⟩

theorem continuous_symbolicLatentSolutionFiberToFeasible
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i) :
    Continuous (symbolicLatentSolutionFiberToFeasible
      S values targets hvalues) := by
  exact continuous_subtype_val.subtype_mk (fun x => by
    intro i
    rw [show (S.observable i) x.1 = values i by exact x.2 i]
    exact hvalues i)

def symbolicLatentSolutionFiberToFeasibleTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i) :
    TopCat.of (symbolicLatentSolutionFiber S values) ⟶
      TopCat.of (feasibleLatentSubspace S targets) :=
  TopCat.ofHom
    { toFun := symbolicLatentSolutionFiberToFeasible S values targets hvalues
      continuous_toFun := continuous_symbolicLatentSolutionFiberToFeasible
        S values targets hvalues }

theorem symbolicLatentSolutionFiberToFeasibleTopCatHom_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i)
    (x : symbolicLatentSolutionFiber S values) :
    symbolicLatentSolutionFiberToFeasibleTopCatHom
      S values targets hvalues x =
      symbolicLatentSolutionFiberToFeasible S values targets hvalues x :=
  rfl

theorem symbolicLatentSolutionFiber_feasible_factorization
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i) :
    symbolicLatentSolutionFiberToFeasibleTopCatHom
        S values targets hvalues ≫
        symbolicLatentFeasibleSubspaceInclusion S targets =
      symbolicLatentSolutionFiberInclusion S values := by
  ext x
  rfl

theorem symbolicLatentSolutionFiberToFeasible_natural
    {X Y ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ)
    (targets : ι → Set ℝ) (hvalues : ∀ i, values i ∈ targets i) :
    symbolicLatentSolutionFiberToFeasibleTopCatHom
          S values targets hvalues ≫
        symbolicLatentFeasibleSubspaceTopCatHom F targets =
      symbolicLatentSolutionFiberTopCatHom F values ≫
        symbolicLatentSolutionFiberToFeasibleTopCatHom
          T values targets hvalues := by
  ext x
  rfl

end InfoGeometry.Topology
