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

This is the literature-owned socket for the infinite Cantor-set Clifford/Fock
representation layer. It records the citation and carries the theorem-backed
topology-side carrier data for the analytic `L^2` model.

No infinite CAR completion.
No CCR completion.
No analytic continuation.
No Hilbert--Polya claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket

open InfoGeometry.Topology.FractalCantorFockWitness

/--
The literature-owned infinite Cantor/Clifford/Fock socket.

The socket is intentionally thin: it pins the paper citation and stores the
theorem-backed Cantor/Fock carrier data as the owner lane.
-/
@[socket_debt_tag]
structure InfiniteCantorCliffordFockSocket
    (Op E : Type*) [Ring Op]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  citationAuthors : String := "Derya Çelik and Şahin Koçak"
  citationTitle :
    String :=
    "A Fractal Representation of the Complex Clifford Algebra Equivalent to the Fock Representation"
  citationVenue : String := "Advances in Applied Clifford Algebras"
  citationYear : Nat := 2011
  carrierData : CelikKocakInfiniteFockCarrierData E

/-- The socket exposes the underlying carrier data. -/
@[rep_depth operator]
def carrierData_readout {Op E : Type*} [Ring Op]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : InfiniteCantorCliffordFockSocket Op E) :
    CelikKocakInfiniteFockCarrierData E :=
  S.carrierData

end InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket
