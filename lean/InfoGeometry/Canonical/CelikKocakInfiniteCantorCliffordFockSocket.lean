import Mathlib.Tactic
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Topology.FractalCantorFockWitness

/-!
# InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket

Literature owner:
  Derya Çelik and Şahin Koçak,
  "A Fractal Representation of the Complex Clifford Algebra Equivalent to the
  Fock Representation",
  Advances in Applied Clifford Algebras, 2011.

This is the literature-owned socket for the Cantor-set Clifford/Fock
representation layer. It records the citation and carries the theorem-backed
topology-side carrier data for the finite-coordinate `L^2` model used in the
repository.

No CAR completion claim.
No CCR completion.
No analytic continuation.
No Hilbert--Polya claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket

open InfoGeometry.Topology.FractalCantorFockWitness

/--
The literature-owned Cantor/Clifford/Fock socket.

The socket is intentionally thin: it pins the paper citation and stores the
theorem-backed Cantor/Fock carrier data as the owner lane.
-/
structure InfiniteCantorCliffordFockSocket
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  carrierData : CelikKocakInfiniteFockCarrierData E

/-- The socket exposes the underlying carrier data. -/
@[rep_depth operator]
def carrierData_readout {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : InfiniteCantorCliffordFockSocket E) :
    CelikKocakInfiniteFockCarrierData E :=
  S.carrierData

end InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket
