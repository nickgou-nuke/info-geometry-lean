import InfoGeometry.Topology.DelaunayFlipInterfaces
import InfoGeometry.Topology.PureBraidGroup

/-!
# Delaunay pure braid representation boundary

This file consumes the proven Delaunay quotient layer.  It exposes two separate
boundary surfaces:

* a quotient/factorization readout from `PB_{moving+3}` to Delaunay flip-word
  quotient matrices;
* the intended final matrix-unit homomorphism type
  `PB_{moving+3} →* Units (Matrix (Fin (2*moving+1)) (Fin (2*moving+1)) ℚ)`.

It does not prove that Rohozhkin generator matrices satisfy the presented pure
braid relators, and it does not claim Markov invariance.
-/

namespace InfoGeometry.Topology.RohozhkinBoundary

open InfoGeometry.Topology.Delaunay

/-- Matrix readout for a supplied map from the presented source PB to the flip-word quotient. -/
def rohozhkinPureBraidMatrix {moving : ℕ}
    (boundary : PureBraidQuotientBoundary moving) :
    RohozhkinSourcePB moving → Matrix (Fin (rohozhkinDim moving)) (Fin (rohozhkinDim moving)) ℚ :=
  fun g => rohozhkinQuotientMatrix (boundary.braidToQuotient g)

/-- Quotient/factorization readback theorem for the supplied boundary map. -/
theorem rohozhkin_respects_pure_braid_presentation {moving : ℕ}
    (boundary : PureBraidQuotientBoundary moving) (g : RohozhkinSourcePB moving) :
    rohozhkinPureBraidMatrix boundary g =
      rohozhkinQuotientMatrix (boundary.braidToQuotient g) :=
  rfl

/-- The final target shape for a closed Rohozhkin pure-braid representation theorem. -/
abbrev RohozhkinGLBoundary (moving : ℕ) :=
  PureBraidRepresentationBoundary moving

end InfoGeometry.Topology.RohozhkinBoundary
