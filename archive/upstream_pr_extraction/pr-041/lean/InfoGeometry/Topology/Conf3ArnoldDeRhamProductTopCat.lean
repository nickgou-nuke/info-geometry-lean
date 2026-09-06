import InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopological

/-!
# `TopCat` packaging for the Conf₃ braid-shadow / de Rham product packet

This file packages the discrete product packet as a `TopCat` object and records
its two coordinate projections.  It does not identify the braid-shadow carrier
with the de Rham candidate carrier.
-/

noncomputable section

namespace InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopCat

open CategoryTheory
open InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopological

variable {R : Type*} [CommRing R]
variable (D : ℕ)

/-- Projection to the braid-shadow factor. -/
def projectionBraidShadow :
    TopCat.of (Conf3ArnoldDeRhamProductPacket R D) ⟶
      TopCat.of
        (InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.Conf3ArnoldBraidShadowPacket R) := by
  refine TopCat.ofHom ?_
  refine ⟨Prod.fst, continuous_of_discreteTopology⟩

theorem projectionBraidShadow_apply
    (p : Conf3ArnoldDeRhamProductPacket R D) :
    projectionBraidShadow (R := R) D p = p.1 := by
  rfl

/-- Projection to the de Rham-candidate factor. -/
def projectionDeRhamCandidate :
    TopCat.of (Conf3ArnoldDeRhamProductPacket R D) ⟶
      TopCat.of
        (ULift (InfoGeometry.Topology.Conf3DeRhamCandidateTopological.Conf3DeRhamCandidatePacket
          D)) := by
  refine TopCat.ofHom ?_
  refine ⟨fun p => ULift.up p.2, continuous_of_discreteTopology⟩

theorem projectionDeRhamCandidate_apply
    (p : Conf3ArnoldDeRhamProductPacket R D) :
    projectionDeRhamCandidate (R := R) D p = ULift.up p.2 := by
  rfl

end InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopCat
