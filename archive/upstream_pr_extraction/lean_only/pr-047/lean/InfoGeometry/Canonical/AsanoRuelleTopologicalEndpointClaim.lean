import InfoGeometry.AsanoRuelle.TopologicalEndpoint
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/-!
# Public claim adapter for the Asano--Ruelle topological endpoint

The concrete pole argument proves the left endpoint under the necessary
origin-avoidance hypothesis `0 ∉ K₁`.  This file exposes that result at the
public claim boundary without strengthening the claim definition itself.
-/

namespace InfoGeometry.Canonical.AsanoRuelleTopologicalEndpointClaim

open Set
open InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/--
The canonical bounded-pole argument inhabits the public endpoint claim.

The contracted-root equation `hQ` is intentionally unused: the endpoint
alternative is a property of the coefficient matrix and the zero-free sets;
the equation is carried by the public claim for downstream consumers.
-/
theorem asanoRuelleTopologicalEndpointClaim_of_no_zero_left
    (K1 K2 : Set ℂ)
    (hK1_closed : IsClosed K1)
    (hK2_closed : IsClosed K2)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (A B C D z : ℂ)
    (hPhi_zerofree :
      ∀ z1 z2, z1 ∉ K1 → z2 ∉ K2 →
        A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hQ : A + D * z = 0) :
    InfoGeometry.AsanoRuelle.asanoRuelleTopologicalEndpointClaim
      K1 K2 B C D := by
  exact asano_endpoint_disjunction_left
    A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd
    hK1_no_zero hPhi_zerofree

end InfoGeometry.Canonical.AsanoRuelleTopologicalEndpointClaim
