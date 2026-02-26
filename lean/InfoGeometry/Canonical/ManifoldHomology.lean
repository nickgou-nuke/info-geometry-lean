import InfoGeometry.Experimental.AssumptionWrappers.ManifoldHomology

/-!
# Research.ManifoldHomology

Compatibility forwarder over
`InfoGeometry.Experimental.AssumptionWrappers.ManifoldHomology`.
-/

namespace InfoGeometry.Canonical.ManifoldHomology

/-!
Explicitly forward manifold homology/degree scaffold surfaces from the
experimental wrapper.
-/
export InfoGeometry.Experimental.AssumptionWrappers.ManifoldHomology (
  IsRegularValue
  topHomologyIso
  top_homology_is_Z
  top_homology_is_Z_true
  mappingDegree
  mappingDegree_nonneg
  degree_formula_via_jacobian
  degree_formula_via_jacobian_true
  exists_isolating_nhds_of_nondegenerate
  preimage_finite_of_regular_value
  exists_local_chart_homotopy_to_linear
  local_degree_eq_sign_jacDet
)

end InfoGeometry.Canonical.ManifoldHomology
