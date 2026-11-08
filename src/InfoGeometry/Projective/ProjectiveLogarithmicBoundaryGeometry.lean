/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Projective.CrossRatio
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.Quadrics.PluckerKlein
import InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.CanonicalFormBoundaryResidue

/-!
# Projective logarithmic boundary geometry

Compatibility aggregate for the upstream module path. The canonical owners
for cross-ratio, Plücker/Klein, Arnold–Cohen, and residue remain the imported
modules above. Exterior-algebra alternation and decomposable-blade square-zero
are owned separately by Mathlib and
`InfoGeometry.GrassmannianTower.decomposable_exterior_blade_square_zero`;
this aggregate introduces no duplicate carrier or theorem owner.
-/
