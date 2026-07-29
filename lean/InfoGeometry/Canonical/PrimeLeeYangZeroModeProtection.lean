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

/-! The defect-free limit carrier is the supplied completed-xi readout itself;
the former packet added no field or law. -/
@[socket_debt_tag]
abbrev DefectFreeLimitPacket (CompletedXiReadout : Type) := CompletedXiReadout

@[socket_debt_tag]
abbrev ZeroModeProtectionPacket
    (CompletedXiReadout ProtectionReadout : Type) :=
  DefectFreeLimitPacket CompletedXiReadout × ProtectionReadout

namespace ZeroModeProtectionPacket

variable {CompletedXiReadout ProtectionReadout : Type}
variable
  (P : ZeroModeProtectionPacket
    CompletedXiReadout ProtectionReadout)

abbrev defectFreeLimit :
    DefectFreeLimitPacket CompletedXiReadout :=
  P.1

abbrev protectionReadout : ProtectionReadout :=
  P.2

end ZeroModeProtectionPacket

end InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
