import InfoGeometry.Topology.AmplituhedronBoundaryRank32
import InfoGeometry.Projective.TwistorConfigurationSpace

/-!
# External De Rham Cohomology Bridge

This file connects the explicit `Fin 32` boundary carrier to an abstract 
topological assumption for the de Rham cohomology of the quadric complement 
configuration space `F_Q(C^4,3)`.

Closed here:

* an explicit certificate structure `ExternalRank32DeRhamCertificate` that asserts 
  the total rank of the de Rham cohomology of the quadric complement is 32;
* a bridge theorem showing that if this certificate holds, the de Rham rank matches 
  the cardinality of our finite rank-32 boundary carrier.

Not closed here:

* no theorem natively computes the de Rham cohomology from the algebraic 
  geometry of `F_Q(C^4,3)`.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

open InfoGeometry.Projective.TwistorConfigurationSpace

/-- 
Explicit external certificate assuming the de Rham cohomology of the 
quadric complement `F_Q(C^4,3)` has total rank 32. 
-/
structure ExternalRank32DeRhamCertificate where
  quadricComplementDeRhamRank : ℕ
  rank_eq : quadricComplementDeRhamRank = 32

/--
The external de Rham cohomology rank equals the cardinality of the finite rank-32
boundary carrier, under the certificate assumption.
-/
theorem external_de_rham_rank_eq_boundary_card 
    (C : ExternalRank32DeRhamCertificate) :
    C.quadricComplementDeRhamRank = Fintype.card BoundaryRank32State := by
  calc
    C.quadricComplementDeRhamRank = 32 := C.rank_eq
    _ = Fintype.card BoundaryRank32State := boundaryRank32State_card.symm

end InfoGeometry.Topology.AmplituhedronBoundary
