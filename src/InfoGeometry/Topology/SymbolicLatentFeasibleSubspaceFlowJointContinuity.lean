import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHausFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Joint continuity on a feasible symbolic-latent subspace

The ambient symbolic-latent flow is jointly continuous in time and state.
This owner restricts that action to the closed feasible subtype and proves
joint continuity of the resulting subtype-valued action directly.
-/

noncomputable section

namespace InfoGeometry.Topology

variable {X ι : Type} [TopologicalSpace X] [Fintype ι]

theorem SymbolicLatentFlow.continuous_feasibleSubspaceFlow
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ) :
    Continuous (fun p : ℝ × feasibleLatentSubspace S targets =>
      F.feasibleSubspaceMap p.1 targets p.2) := by
  exact (F.continuous_act.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
    (fun p => F.maps_feasibleSet p.1 targets
      ⟨p.2, p.2.property, rfl⟩)

@[simp] theorem SymbolicLatentFlow.feasibleSubspaceFlow_apply
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (p : ℝ × feasibleLatentSubspace S targets) :
    F.feasibleSubspaceMap p.1 targets p.2 =
      ⟨F.act p.1 (p.2 : X),
        F.maps_feasibleSet p.1 targets ⟨p.2, p.2.property, rfl⟩⟩ :=
  rfl

theorem SymbolicLatentFlow.feasibleSubspaceFlow_preserves_observation
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (targets : ι → Set ℝ)
    (t : ℝ)
    (x : feasibleLatentSubspace S targets) :
    symbolicObservationMap S (F.feasibleSubspaceMap t targets x) =
      symbolicObservationMap S x := by
  exact F.preserves_observation t x

end InfoGeometry.Topology

