/-
InfoGeometry/Geometry/SplitOrthogonalSpace.lean

Explicit split-orthogonal base-space carrier for the Narain / O(n,n) tower.
No complex imports.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebraic.SplitQuadraticForm

noncomputable section

namespace InfoGeometry.Geometry.Cartan

open InfoGeometry.Algebraic.SplitSignature

/--
Typed split-orthogonal Cartan stage carrier.

The carrier and its topology are explicit data. This owner does not identify
the data with the analytic symmetric space `O(n,n)/(O(n) × O(n))`; that
identification requires a separate matrix/quotient construction.
-/
structure SplitOrthogonalCartanSpace (_n : ℕ) where
  carrier : Type
  topology : TopologicalSpace carrier

/--
Typed boundary carrier paired with a split-orthogonal stage.

No isotropic or quotient property is assumed by the type itself; those are
separate theorem-level hypotheses for downstream boundary results.
-/
structure SplitOrthogonalBoundary (_n : ℕ) where
  carrier : Type
  topology : TopologicalSpace carrier

end InfoGeometry.Geometry.Cartan
