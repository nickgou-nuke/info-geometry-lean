import InfoGeometry.Canonical.PrimeMertensDefectBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

Readout and topological-protection data layer for the prime Lee--Yang program.

This module records only the concrete readout data for the defect-free prime
Lee--Yang limit.  Half-filling, zero-energy, unbroken SUSY, topological
protection, and matching to completed `xi` zeros must be proved in concrete
downstream owner files; they are not stored as arbitrary proposition fields
here.

It deliberately does not prove that Riemann zeros are Majorana zero modes, does
not prove RH, and does not turn the inverse-zeta Witten character into a
completed-`xi` determinant.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

@[socket_debt_tag]
structure ZeroModeProtectionPacket
    (CompletedXiReadout ProtectionReadout : Type) where
  defectFreeLimit : CompletedXiReadout
  protectionReadout : ProtectionReadout

end InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
