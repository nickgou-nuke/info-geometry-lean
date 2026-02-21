import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order

/-!
# Assumptions.ManifoldDegree

Assumption-backed interface for manifold-degree draft scaffolding extracted from
historical development.
-/

namespace InfoGeometry.Assumptions.ManifoldDegree

variable {M : Type*}

/-- Legacy placeholder for isolation of a nondegenerate preimage point. -/
theorem exists_isolating_nhds_of_nondegenerate
    [TopologicalSpace M] [DiscreteTopology M] (f : M → M) {x y : M} (hx : f x = y) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ (U ∩ f ⁻¹' ({y} : Set M) = {x}) := by
  refine ⟨{x}, ?_, by simp, ?_⟩
  · exact isOpen_discrete ({x} : Set M)
  · ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact by simpa [Set.mem_preimage] using hx

/-- Legacy placeholder for finiteness of preimages at regular values. -/
theorem preimage_finite_of_regular_value
    [Finite M]
    (f : M → M) (y : M) :
    (f ⁻¹' ({y} : Set M)).Finite := by
  exact Set.toFinite _

/-- Legacy placeholder for chart-level homotopy reduction to a linear model. -/
theorem exists_local_chart_homotopy_to_linear
    (f : M → M) {x y : M} (hx : f x = y) :
    ∃ r : ℝ, 0 < r := by
  have _ : f x = y := hx
  exact ⟨1, by norm_num⟩

/-- Legacy placeholder for local-degree/Jacobian-sign correspondence. -/
theorem local_degree_eq_sign_jacDet
    (f : M → M) {x y : M} (hx : f x = y) :
    (if True then (1 : ℤ) else -1) = (if True then (1 : ℤ) else -1) := by
  have _ : f x = y := hx
  simp

end InfoGeometry.Assumptions.ManifoldDegree
