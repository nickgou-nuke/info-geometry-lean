import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of feasible symbolic-latent subspaces

This file packages the already-verified feasible subtype as a `CompHaus`
object under compactness of the ambient carrier and closedness of the target
sets.  It does not add new analytic structure or new quotient carriers.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Fintype ι]

noncomputable def symbolicLatentFeasibleSubspaceCompHaus
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) : CompHaus := by
  letI : CompactSpace (feasibleLatentSubspace S targets) :=
    (isClosed_finiteSymbolicLatentSystem_feasibleSet S targets hclosed
      ).isClosedEmbedding_subtypeVal.compactSpace
  exact CompHaus.of (feasibleLatentSubspace S targets)

noncomputable def symbolicLatentFeasibleSubspaceCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    TopCat.of (feasibleLatentSubspace S targets) ⟶
      compHausToTop.obj (symbolicLatentFeasibleSubspaceCompHaus S targets hclosed) := by
  exact TopCat.ofHom
    { toFun := id
      continuous_toFun := continuous_id }

theorem symbolicLatentFeasibleSubspaceCompHausTopCatHom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleSubspaceCompHausTopCatHom S targets hclosed x = x :=
  rfl

theorem symbolicLatentFeasibleSubspaceCompHausTopCatHom_isIso
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsIso (symbolicLatentFeasibleSubspaceCompHausTopCatHom S targets hclosed) := by
  simpa [symbolicLatentFeasibleSubspaceCompHausTopCatHom] using
    (inferInstance : IsIso (𝟙 (TopCat.of (feasibleLatentSubspace S targets))))

end InfoGeometry.Topology
