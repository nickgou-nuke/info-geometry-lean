import InfoGeometry.Topology.AmplituhedronBoundaryRank32
import InfoGeometry.Projective.TwistorConfigurationSpace

/-!
# External De Rham Cohomology Bridge

This file connects the explicit `Fin 32` boundary carrier to an abstract 
topological property for the de Rham cohomology of the quadric complement 
configuration space `F_Q(C^4,3)`.

Closed here:

* a bridge theorem showing that if the external rank equals 32, the de Rham rank matches
  the cardinality of our finite rank-32 boundary carrier.

Not closed here:

* no theorem natively computes the de Rham cohomology from the algebraic 
  geometry of `F_Q(C^4,3)`.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

open InfoGeometry.Projective.TwistorConfigurationSpace

/--
The external de Rham cohomology rank equals the cardinality of the finite rank-32
boundary carrier, under the property property.
-/
theorem external_de_rham_rank_eq_boundary_card
    (quadricComplementDeRhamRank : ℕ)
    (hRank : quadricComplementDeRhamRank = 32) :
    quadricComplementDeRhamRank = Fintype.card BoundaryRank32State := by
  calc
    quadricComplementDeRhamRank = 32 := hRank
    _ = Fintype.card BoundaryRank32State := boundaryRank32State_card.symm

end InfoGeometry.Topology.AmplituhedronBoundary
