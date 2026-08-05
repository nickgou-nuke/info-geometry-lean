import InfoGeometry.Canonical.PrimeMertensDefectBoundary
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
abbrev ZeroModeProtectionPacket
    (CompletedXiReadout ProtectionReadout : Type) :=
  CompletedXiReadout × ProtectionReadout

namespace ZeroModeProtectionPacket

def defectFreeLimit
    {CompletedXiReadout ProtectionReadout : Type}
    (P : ZeroModeProtectionPacket CompletedXiReadout ProtectionReadout) :
    CompletedXiReadout := P.1

def protectionReadout
    {CompletedXiReadout ProtectionReadout : Type}
    (P : ZeroModeProtectionPacket CompletedXiReadout ProtectionReadout) :
    ProtectionReadout := P.2

end ZeroModeProtectionPacket

end InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
