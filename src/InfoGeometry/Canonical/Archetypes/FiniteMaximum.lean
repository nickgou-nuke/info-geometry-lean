import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex

open TopologicalSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem continuous_attains_finiteMaximum
    (f : Convexity.StdSimplex ℝ ι → ℝ) (hf : Continuous f) :
    ∃ x : Convexity.StdSimplex ℝ ι, ∀ y : Convexity.StdSimplex ℝ ι, f y ≤ f x := by
  classical
  let : CompactSpace (Convexity.StdSimplex ℝ ι) :=
    Convexity.StdSimplex.compactSpace ℝ ι
  let : Nonempty (Convexity.StdSimplex ℝ ι) :=
    ⟨Convexity.StdSimplex.single (Classical.choice ‹Nonempty ι›)⟩
  obtain ⟨x, -, hx_max⟩ :=
    IsCompact.exists_isMaxOn (α := ℝ) (s := (Set.univ : Set (Convexity.StdSimplex ℝ ι)))
      isCompact_univ Set.univ_nonempty (Continuous.continuousOn hf)
  exact ⟨x, fun y => hx_max (Set.mem_univ y)⟩
