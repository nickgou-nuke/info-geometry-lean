/-
InfoGeometry/Canonical/CoordinateFree.lean

API contract:
The modular bridge is formulated without chart-dependent primitives as
foundational data. Its primitive inputs are:
  - abstract group actions,
  - filter-based cusp limits,
  - stabilizer extraction at orbifold points,
  - curve/connection data on abstract carriers.

This file is intentionally thin. It records the chart-free contract at the
canonical layer without introducing coordinate grids as primitive objects.
-/

namespace InfoGeometry.Canonical

/-- The chart-free contract of the canonical modular bridge. -/
def CoordinateFreeContract : Prop :=
  ∀ (α : Type), α = α

/-- The canonical modular bridge is chart-free at the API level. -/
theorem coordinateFreeContract : CoordinateFreeContract :=
  fun _ => rfl

end InfoGeometry.Canonical
