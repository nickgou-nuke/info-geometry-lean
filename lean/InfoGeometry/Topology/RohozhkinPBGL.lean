import InfoGeometry.Topology.DelaunayPureBraidRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Rohozhkin PB → GL boundary

Thin boundary alias for the Delaunay pure-braid representation layer.
-/

namespace InfoGeometry.Topology.RohozhkinPBGL

open InfoGeometry.Topology.RohozhkinBoundary

/-- The GL target type for Rohozhkin representations. -/
abbrev RohozhkinGLBoundary (moving : ℕ) :=
  RohozhkinMatrixUnits moving

end InfoGeometry.Topology.RohozhkinPBGL
