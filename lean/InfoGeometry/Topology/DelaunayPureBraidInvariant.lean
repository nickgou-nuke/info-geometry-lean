import Mathlib.Algebra.Group.Basic
import InfoGeometry.Topology.RohozhkinPentagonMatrix

namespace InfoGeometry.Topology.Delaunay

/-- A sequence of abstract Delaunay flips -/
structure DelaunayFlipWord (n : ℕ) where
  -- flips : List FlipContext
  admissible : Prop

end InfoGeometry.Topology.Delaunay
