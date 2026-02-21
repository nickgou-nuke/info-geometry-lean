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

export InfoGeometry.Assumptions.ManifoldHomology (
  IsRegularValue
  top_homology_is_Z
  topHomologyIso
  mappingDegree
  degree_formula_via_jacobian
)

export InfoGeometry.ManifoldTopology (
  exists_isolating_nhds_of_nondegenerate
  preimage_finite_of_regular_value
  exists_local_chart_homotopy_to_linear
  local_degree_eq_sign_jacDet
)

end InfoGeometry.Research.ManifoldHomology

