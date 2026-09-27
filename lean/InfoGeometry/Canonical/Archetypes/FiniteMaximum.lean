import InfoGeometry.Core.ProjectiveSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex

open TopologicalSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem continuous_attains_finiteMaximum (f : (stdSimplex ℝ ι) → ℝ) (hf : Continuous f) :
  ∃ x : stdSimplex ℝ ι, ∀ y : stdSimplex ℝ ι, f y ≤ f x := by
  haveI : CompactSpace (stdSimplex ℝ ι) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ι)
  obtain ⟨x, -, hx_max⟩ := IsCompact.exists_isMaxOn (α := ℝ) (s := (Set.univ : Set (stdSimplex ℝ ι)))
    isCompact_univ Set.univ_nonempty (Continuous.continuousOn hf)
  exact ⟨x, fun y => hx_max (Set.mem_univ y)⟩
