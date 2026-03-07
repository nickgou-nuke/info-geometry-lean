import InfoGeometry.Canonical.ManifoldHomology

/-!
# Assumptions.ManifoldHomology

DEPRECATED compatibility shim.

New code should import:
- `InfoGeometry.Canonical.ManifoldHomology`

Compatibility re-export of the canonical manifold-homology core.
This keeps legacy `InfoGeometry.Assumptions.ManifoldHomology.*` paths stable
while removing duplicated definitions.
-/

namespace InfoGeometry.Assumptions.ManifoldHomology

export InfoGeometry.Canonical.ManifoldHomology
  (IsRegularValue
   topHomologyIso
   top_homology_is_Z
   top_homology_is_Z_true
   mappingDegree
   mappingDegree_nonneg
   degree_formula_via_jacobian
   degree_formula_via_jacobian_true)

end InfoGeometry.Assumptions.ManifoldHomology
