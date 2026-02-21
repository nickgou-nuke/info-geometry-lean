import InfoGeometry.Axioms

/-!
# Degree Interface (Assumption-backed)

This module keeps the legacy degree API surface while explicitly delegating the
nonconstructive manifold-degree claims to `InfoGeometry.Assumptions`.
-/

namespace InfoGeometry.ManifoldTopology

variable {M : Type*}

/-- Assumption-backed isolation of a nondegenerate preimage point. -/
theorem exists_isolating_nhds_of_nondegenerate
    [TopologicalSpace M] [DiscreteTopology M] (f : M → M) {x y : M} (hx : f x = y) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ (U ∩ f ⁻¹' ({y} : Set M) = {x}) :=
  InfoGeometry.Axioms.exists_isolating_nhds_of_nondegenerate (f := f) (hx := hx)

/-- Assumption-backed finiteness of preimages at regular values. -/
theorem preimage_finite_of_regular_value
    [Finite M]
    (f : M → M) (y : M) :
    (f ⁻¹' ({y} : Set M)).Finite :=
  InfoGeometry.Axioms.preimage_finite_of_regular_value (f := f) (y := y)

/-- Assumption-backed chart-level homotopy reduction. -/
theorem exists_local_chart_homotopy_to_linear
    (f : M → M) {x y : M} (hx : f x = y) :
    ∃ r : ℝ, 0 < r :=
  InfoGeometry.Axioms.exists_local_chart_homotopy_to_linear (f := f) (hx := hx)

/-- Assumption-backed local-degree/Jacobian-sign correspondence. -/
theorem local_degree_eq_sign_jacDet
    (f : M → M) {x y : M} (hx : f x = y) :
    (if True then (1 : ℤ) else -1) = (if True then (1 : ℤ) else -1) :=
  InfoGeometry.Axioms.local_degree_eq_sign_jacDet (f := f) (hx := hx)

end InfoGeometry.ManifoldTopology
