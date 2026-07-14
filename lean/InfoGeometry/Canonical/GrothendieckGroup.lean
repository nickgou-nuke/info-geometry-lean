import InfoGeometry.Algebra.Grothendieck

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

namespace GrothendieckGroup

/-- Compatibility alias for the owner theorem `Grothendieck ℕ ≃+ ℤ`. -/
noncomputable def grothendieckEquivInt : _root_.Grothendieck ℕ ≃+ ℤ :=
  _root_.grothendieckEquivInt

end GrothendieckGroup
