import InfoGeometry.Core.ProjectiveSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex

open TopologicalSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem continuous_attains_finiteMaximum (f : (stdSimplex ℝ ι) → ℝ) (hf : Continuous f) :
    ∃ x : stdSimplex ℝ ι, ∀ y : stdSimplex ℝ ι, f y ≤ f x := by
  haveI := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ι)
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  exact ⟨x, fun y ↦ hx (Set.mem_univ y)⟩

