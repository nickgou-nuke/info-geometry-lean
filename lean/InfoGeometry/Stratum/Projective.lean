import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Ray
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic

/-!
# InfoGeometry.Stratum.Projective

The foundational Mathlib bridge for projective and ray geometry.

This stratum formalizes the connection between Information Geometry's projective concepts
(like spaces of positive measures modulo scaling) and `Mathlib`'s native
`Projectivization` and `Module.Ray`.

## Functorial Hierarchy
- `PositiveRay V` represents the positive cone projectivization.
- `RealProjectiveSpace V` represents the full projective space (modulo nonzero scalars).
-/

namespace InfoGeometry.Stratum.Projective

/-- Type alias for the positive rays in a real vector space. -/
abbrev PositiveRay (V : Type*) [AddCommGroup V] [Module ℝ V] := Module.Ray ℝ V

/-- Type alias for the full real projective space of a vector space. -/
abbrev RealProjectiveSpace (V : Type*) [AddCommGroup V] [Module ℝ V] := Projectivization ℝ V

end InfoGeometry.Stratum.Projective
