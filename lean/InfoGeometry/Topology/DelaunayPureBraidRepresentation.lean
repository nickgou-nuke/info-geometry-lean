import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Categorical.BraidPermutationQuotient

/-!
# Restricting braid representations to the canonical pure subgroup

The source pure braid group is the kernel of the canonical braid-to-permutation
homomorphism. Any already constructed representation of the full braid group
restricts to this subgroup. This file does not construct a representation from
Delaunay flip matrices: the required map from those matrix transports to the
braid group remains an open development frontier.
-/

namespace InfoGeometry.Topology.RohozhkinBoundary

open InfoGeometry.Topology.Delaunay
open InfoGeometry.Categorical.BraidPermutationQuotient

/-- The full braid group on the point count used by the Rohozhkin parameter. -/
abbrev RohozhkinBraidGroup (moving : ℕ) :=
  Braid.braid_group (moving + 3)

/-- The matrix-unit target for the Rohozhkin dimension associated to `moving`. -/
abbrev RohozhkinMatrixUnits (moving : ℕ) :=
  MatrixUnits (rohozhkinDim moving)

/-- The canonical pure braid kernel on the corresponding number of strands. -/
abbrev RohozhkinPureBraidGroup (moving : ℕ) :=
  RohozhkinSourcePB moving

/-- Restrict a full braid-group representation to the pure braid subgroup. -/
def restrictRohozhkinBraidRepresentation (moving : ℕ)
    (ρ : RohozhkinBraidGroup moving →* RohozhkinMatrixUnits moving) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  ρ.comp (Subgroup.subtype (RohozhkinSourcePB moving))

end InfoGeometry.Topology.RohozhkinBoundary
