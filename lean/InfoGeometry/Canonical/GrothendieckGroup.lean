import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.GrothendieckGroup

Compatibility shim for the Grothendieck-group owner.

The owner construction now lives in `InfoGeometry.Algebra.Grothendieck`.  This
file intentionally re-exports that owner instead of duplicating the global
definitions `Grothendieck`, `grothendieckMap`, `grothendieckLift`, and
`grothendieckEquivInt`.

Keeping the duplicate construction here caused import-order collisions whenever
the algebra owner and this canonical module appeared in the same environment.
-/
