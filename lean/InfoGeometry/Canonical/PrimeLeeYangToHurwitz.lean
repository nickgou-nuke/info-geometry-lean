import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimeLeeYangConvergence

/-!
# InfoGeometry.Canonical.PrimeLeeYangToHurwitz

Relay layer from the prime convergence socket to the Hurwitz zero-transfer
socket.

This file does not prove any prime-to-`xi` convergence statement and does not
prove RH. It isolates the transfer step that comes after the analytic
convergence witness. The Clifford-wavelet layer is imported only as the
candidate source of that convergence witness.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangToHurwitz

open InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimeLeeYangConvergence

/--
Bridge packet from a convergence witness to a Hurwitz transfer witness.

The packet is intentionally explicit: it keeps the convergence data and the
Hurwitz data separate while allowing downstream code to relay the latter.
-/
@[socket_debt_tag, rep_depth operator]
structure PrimeLeeYangToHurwitzWitness
    (Ξ : CompletedXiZeroPredicate)
    (A : LeeYangApproximants) where
  /-- The convergence socket that feeds the Hurwitz relay. -/
  convergence :
    PrimeLeeYangConvergenceSocket Ξ A

  /-- The Hurwitz zero-transfer witness itself. -/
  hurwitz :
    CorrectHurwitzZeroTransferWitness Ξ A

  /-- Guardrail: this relay is conditional and does not prove RH. -/
  no_unconditional_RH_claim_guard : Type

namespace PrimeLeeYangToHurwitzWitness

variable {Ξ : CompletedXiZeroPredicate}
variable {A : LeeYangApproximants}
variable (W : PrimeLeeYangToHurwitzWitness Ξ A)

/-- The relay maps completed-`xi` zeros to the Lee--Yang circle. -/
@[rep_depth operator]
theorem xiZeros_map_to_unit_circle
    (W : PrimeLeeYangToHurwitzWitness Ξ A)
    (s : ℂ)
    (hs_ne_one : s ≠ 1)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) :=
by
  exact corrected_hurwitz_xiZeros_map_to_unit_circle
    W.hurwitz s hs_ne_one hs

end PrimeLeeYangToHurwitzWitness

end InfoGeometry.Canonical.PrimeLeeYangToHurwitz
