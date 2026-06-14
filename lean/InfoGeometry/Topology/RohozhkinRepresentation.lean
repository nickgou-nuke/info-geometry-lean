import InfoGeometry.Topology.DelaunayPureBraidRepresentation
import InfoGeometry.Topology.PureBraidGroup
import InfoGeometry.Topology.RohozhkinPBGL

/-!
# Rohozhkin representation boundary

The final representation boundary for Rohozhkin pure-braid representations,
bridging the presented-group descent theorem to the concrete generator
assignment.
-/

namespace InfoGeometry.Topology.RohozhkinRepresentation

open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.Delaunay

/-- The representation theorem exists when generator matrices satisfy the
presented pure-braid relators. -/
noncomputable def rohozhkinRepresentation (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  pureBraidMatrixRepresentationOfRelators moving gen hrel

end InfoGeometry.Topology.RohozhkinRepresentation
