import InfoGeometry.Assumptions.Determinant

/-!
# Research.Determinant

Domain module for determinant/group-wrapper draft APIs extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- determinant and Jacobian wrapper interface from `InfoGeometry.Assumptions.Determinant`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.Determinant

export InfoGeometry.Assumptions.Determinant (
  GL
  SL
  detHom
  ker_det_eq_SL
  logAbsDet
  jacDet
  jacDet_comp
  jacobian_functoriality
)

end InfoGeometry.Research.Determinant

