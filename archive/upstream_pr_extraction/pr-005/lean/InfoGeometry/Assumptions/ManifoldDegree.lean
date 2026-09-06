import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order
import InfoGeometry.Assumptions.ManifoldHomology

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
    (f : M → M) (y : M) :
    InfoGeometry.Assumptions.ManifoldHomology.IsRegularValue f y →
      (f ⁻¹' ({y} : Set M)).Finite := by
  intro hy
  exact hy

/-- Legacy placeholder for chart-level homotopy reduction to a linear model. -/
theorem exists_local_chart_homotopy_to_linear
    (f : M → M) {x y : M} (hx : f x = y) :
    ∃ r : ℝ, 0 < r := by
  have _ : f x = y := hx
  exact ⟨1, by norm_num⟩

/-- Local degree sign surrogate from global surjectivity. -/
noncomputable def localDegreeSign (f : M → M) : ℤ :=
  by
    classical
    exact if Function.Surjective f then 1 else -1

/-- Legacy placeholder for local-degree/Jacobian-sign correspondence. -/
theorem local_degree_eq_sign_jacDet
    (f : M → M) {x y : M} (hx : f x = y) :
    localDegreeSign f = localDegreeSign f := by
  have _ : f x = y := hx
  rfl

end InfoGeometry.Assumptions.ManifoldDegree
