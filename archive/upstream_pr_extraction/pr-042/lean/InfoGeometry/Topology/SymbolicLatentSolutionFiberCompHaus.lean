import InfoGeometry.Topology.SymbolicLatentSolutionFiberTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff symbolic latent solution fibers

This owner packages the already-closed symbolic latent solution fibers as
compact Hausdorff spaces when the ambient carrier is compact and T2.  It only
records the native subtype and its inclusion into the ambient space.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Fintype ι]

noncomputable def symbolicLatentSolutionFiberCompHaus
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) : CompHaus := by
  letI : CompactSpace (symbolicLatentSolutionFiber S values) :=
    (isClosed_finiteSymbolicLatentSystem_solutionSet S values).isClosedEmbedding_subtypeVal.compactSpace
  exact CompHaus.of (symbolicLatentSolutionFiber S values)

noncomputable def symbolicLatentSolutionFiberCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    TopCat.of (symbolicLatentSolutionFiber S values) ⟶
      compHausToTop.obj (symbolicLatentSolutionFiberCompHaus S values) :=
  TopCat.ofHom
    { toFun := id
      continuous_toFun := continuous_id }

@[simp] theorem symbolicLatentSolutionFiberCompHausTopCatHom_apply
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ)
    (x : symbolicLatentSolutionFiber S values) :
    symbolicLatentSolutionFiberCompHausTopCatHom S values x = x :=
  rfl

theorem symbolicLatentSolutionFiberCompHausTopCatHom_isIso
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    IsIso (symbolicLatentSolutionFiberCompHausTopCatHom S values) := by
  simpa [symbolicLatentSolutionFiberCompHausTopCatHom] using
    (inferInstance : IsIso (𝟙 (TopCat.of (symbolicLatentSolutionFiber S values))))

end InfoGeometry.Topology
