import InfoGeometry.ErlangenLanglandsLane
import InfoGeometry.ErlangenLanglandsGeometryLane

/-!
Geometry-augmented lane entrypoint.

Import this module when a file needs the geometry payload layer together with the
core lane declarations and constructor.
-/

namespace InfoGeometry

namespace ErlangenLanglandsGeometryEntry

/-- Sentinel declaration confirming geometry-lane import reached. -/
theorem loaded : True := by
  trivial

end ErlangenLanglandsGeometryEntry

end InfoGeometry

