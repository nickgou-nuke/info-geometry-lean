import InfoGeometry.Assumptions.ManifoldHomology
import InfoGeometry.Degree

/-!
# Experimental.AssumptionWrappers.ManifoldHomology

Experimental wrapper over:
- `InfoGeometry.Assumptions.ManifoldHomology`
- `InfoGeometry.ManifoldTopology` (from `InfoGeometry.Degree`)

This is the canonical migration home for legacy `Research.ManifoldHomology`
forwarding.
-/

namespace InfoGeometry.Experimental.AssumptionWrappers.ManifoldHomology

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

end InfoGeometry.Experimental.AssumptionWrappers.ManifoldHomology

