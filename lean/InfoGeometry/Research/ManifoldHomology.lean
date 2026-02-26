import InfoGeometry.Assumptions.ManifoldHomology
import InfoGeometry.Degree

/-!
# Research.ManifoldHomology

Domain module for manifold-degree/homology draft APIs extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- explicit scaffold layer from `InfoGeometry.Assumptions.ManifoldHomology`
- legacy degree bridge names from `InfoGeometry.Degree`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.ManifoldHomology

variable {M : Type*}

@[deprecated InfoGeometry.Assumptions.ManifoldHomology.IsRegularValue (since := "2026-02-25")]
abbrev IsRegularValue (f : M → M) (y : M) : Prop :=
  InfoGeometry.Assumptions.ManifoldHomology.IsRegularValue f y

@[deprecated InfoGeometry.Assumptions.ManifoldHomology.top_homology_is_Z (since := "2026-02-25")]
abbrev top_homology_is_Z (M : Type*) : Prop :=
  InfoGeometry.Assumptions.ManifoldHomology.top_homology_is_Z M

@[deprecated InfoGeometry.Assumptions.ManifoldHomology.topHomologyIso (since := "2026-02-25")]
abbrev topHomologyIso (M : Type*) : Type :=
  InfoGeometry.Assumptions.ManifoldHomology.topHomologyIso M

@[deprecated InfoGeometry.Assumptions.ManifoldHomology.mappingDegree (since := "2026-02-25")]
noncomputable abbrev mappingDegree {N : Type*} (f : M → N) : ℤ :=
  InfoGeometry.Assumptions.ManifoldHomology.mappingDegree f

@[deprecated InfoGeometry.Assumptions.ManifoldHomology.degree_formula_via_jacobian (since := "2026-02-25")]
abbrev degree_formula_via_jacobian (f : M → M) (y : M)
    (hy : InfoGeometry.Assumptions.ManifoldHomology.IsRegularValue f y) : Prop :=
  InfoGeometry.Assumptions.ManifoldHomology.degree_formula_via_jacobian f y hy

@[deprecated InfoGeometry.ManifoldTopology.exists_isolating_nhds_of_nondegenerate (since := "2026-02-25")]
theorem exists_isolating_nhds_of_nondegenerate
    [TopologicalSpace M] [DiscreteTopology M]
    (f : M → M) {x y : M} (hx : f x = y) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ (U ∩ f ⁻¹' ({y} : Set M) = {x}) :=
  InfoGeometry.ManifoldTopology.exists_isolating_nhds_of_nondegenerate (f := f) (hx := hx)

@[deprecated InfoGeometry.ManifoldTopology.preimage_finite_of_regular_value (since := "2026-02-25")]
theorem preimage_finite_of_regular_value
    (f : M → M) (y : M)
    (hy : InfoGeometry.Assumptions.ManifoldHomology.IsRegularValue f y) :
    (f ⁻¹' ({y} : Set M)).Finite :=
  InfoGeometry.ManifoldTopology.preimage_finite_of_regular_value (f := f) (y := y) hy

@[deprecated InfoGeometry.ManifoldTopology.exists_local_chart_homotopy_to_linear (since := "2026-02-25")]
theorem exists_local_chart_homotopy_to_linear
    (f : M → M) {x y : M} (hx : f x = y) :
    ∃ r : ℝ, 0 < r :=
  InfoGeometry.ManifoldTopology.exists_local_chart_homotopy_to_linear (f := f) (hx := hx)

@[deprecated InfoGeometry.ManifoldTopology.local_degree_eq_sign_jacDet (since := "2026-02-25")]
theorem local_degree_eq_sign_jacDet
    (f : M → M) {x y : M} (hx : f x = y) :
    InfoGeometry.Axioms.localDegreeSign f = InfoGeometry.Axioms.localDegreeSign f :=
  InfoGeometry.ManifoldTopology.local_degree_eq_sign_jacDet (f := f) (hx := hx)

end InfoGeometry.Research.ManifoldHomology
