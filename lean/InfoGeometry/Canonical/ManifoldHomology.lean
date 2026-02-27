import InfoGeometry.Assumptions.ManifoldHomology
import InfoGeometry.Degree

/-!
# InfoGeometry.Canonical.ManifoldHomology

Canonical manifold-homology surface built from:
- `InfoGeometry.Assumptions.ManifoldHomology`
- `InfoGeometry.ManifoldTopology` (exposed through `InfoGeometry.Degree`)
-/

namespace InfoGeometry.Canonical.ManifoldHomology

/-!
Explicitly forward manifold homology/degree scaffold surfaces from the
assumptions + degree layers.
-/
export InfoGeometry.Assumptions.ManifoldHomology (
  IsRegularValue
  topHomologyIso
  top_homology_is_Z
  top_homology_is_Z_true
  mappingDegree
  mappingDegree_nonneg
  degree_formula_via_jacobian
  degree_formula_via_jacobian_true
)

export InfoGeometry.ManifoldTopology (
  exists_isolating_nhds_of_nondegenerate
  preimage_finite_of_regular_value
  exists_local_chart_homotopy_to_linear
  local_degree_eq_sign_jacDet
)

end InfoGeometry.Canonical.ManifoldHomology
