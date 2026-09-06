import InfoGeometry.Canonical.DeformedIdeleAction
import InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

/-!
# Idele/Cuntz boundary exports

This module is deliberately only an export surface.  The repository does not
yet own a construction of the idele class group, the infinite Cuntz algebra,
or a KMS state on their interaction.  Those claims therefore do not belong in
this file as assumed structures or proposition-valued evidence fields.

The finite Cuntz branch algebra is owned by `DeformedIdeleAction`, while the
currently available arithmetic scaling and zeta readouts are owned by
`IdeleClassZetaSymmetry`.  Downstream code must import those owners directly
for the corresponding theorems.
-/
