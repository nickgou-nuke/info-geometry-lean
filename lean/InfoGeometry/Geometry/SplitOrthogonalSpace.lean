/-
InfoGeometry/Geometry/SplitOrthogonalSpace.lean

Explicit split-orthogonal base-space carrier for the Narain / O(n,n) tower.
No complex imports.
-/

import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebraic.SplitQuadraticForm

noncomputable section

namespace InfoGeometry.Geometry.Cartan

open InfoGeometry.Algebraic.SplitSignature

/--
Abstract split-orthogonal Cartan base space.

This is the formal placeholder for the symmetric space
`O(n,n)/(O(n) × O(n))`. The concrete matrix model can be added later without
changing the downstream cocycle or boundary APIs.
-/
structure SplitOrthogonalCartanSpace (n : ℕ) where
  carrier : Type
  instTopologicalSpace : TopologicalSpace carrier

attribute [instance] SplitOrthogonalCartanSpace.instTopologicalSpace

/--
Abstract isotropic boundary carrier for split-orthogonal degeneration.

This is the natural boundary/readout object paired with
`SplitOrthogonalCartanSpace`.
-/
structure SplitOrthogonalBoundary (n : ℕ) where
  carrier : Type
  instTopologicalSpace : TopologicalSpace carrier

attribute [instance] SplitOrthogonalBoundary.instTopologicalSpace

end InfoGeometry.Geometry.Cartan
