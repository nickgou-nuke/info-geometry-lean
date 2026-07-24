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

/--
Readout packet for the defect-free prime Lee--Yang limit.

Spectral and analytic claims remain outside this data carrier as explicit
theorems in the corresponding owner files.
-/
@[socket_debt_tag]
structure DefectFreeLimitPacket (CompletedXiReadout : Type) where
  completedXiReadout : CompletedXiReadout

@[socket_debt_tag]
structure ZeroModeProtectionPacket
    (CompletedXiReadout ProtectionReadout : Type) where
  /-- Defect-free Lee--Yang/large-deviation limit packet. -/
  defectFreeLimit :
    DefectFreeLimitPacket CompletedXiReadout

  /-- Extra readout for topological protection data. -/
  protectionReadout :
    ProtectionReadout

namespace ZeroModeProtectionPacket

variable {CompletedXiReadout ProtectionReadout : Type}
variable
  (P : ZeroModeProtectionPacket
    CompletedXiReadout ProtectionReadout)

end ZeroModeProtectionPacket

end InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
