import InfoGeometry.Canonical.AffineOrthogonal55Semidirect
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compatibility import for the affine orthogonal `55` layer

The canonical carrier is the native Mathlib semidirect product in
`AffineOrthogonal55Semidirect`.  The former file contained a second hand-built
`Group` on `V55 × OrthogonalGroup55`; that duplicate carrier has been removed.
Downstream users should import `AffineOrthogonal55Semidirect` directly.
-/
