import InfoGeometry.Topology.DelaunayPureBraidRepresentation

/-!
# Rohozhkin PB → GL boundary

Thin boundary alias for the Delaunay pure-braid representation layer.
-/

namespace RohozhkinPBGL

open InfoGeometry.Topology.RohozhkinBoundary

/-- The GL target type for Rohozhkin representations. -/
abbrev RohozhkinGLBoundary (moving : ℕ) :=
  RohozhkinMatrixUnits moving

end RohozhkinPBGL
