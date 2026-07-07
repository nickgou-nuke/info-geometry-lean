import InfoGeometry.Arithmetic.PrimeMajoranaCARGate
import InfoGeometry.Canonical.PrimeMertensDefectBoundary
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

Zero-mode and topological-protection data layer for the prime Lee--Yang
program.

This module records only the data needed to discuss the QFT/SUSY
interpretation of the defect-free prime Lee--Yang limit.  Half-filling,
zero-energy, unbroken SUSY, topological protection, and matching to completed
`xi` zeros must be proved in concrete downstream models; they are not stored as
proposition fields here.

It deliberately does not prove that Riemann zeros are Majorana zero modes, does
not prove RH, and does not turn the inverse-zeta Witten character into a
completed-`xi` determinant.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

open InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
open InfoGeometry.Canonical.PrimeLeeYangDefectFreeLimit

/--
Protection packet for the zero-energy interpretation of the defect-free prime
Lee--Yang limit.

The packet links three already-separated layers:

* a defect-free Lee--Yang/large-deviation/`xi` limit packet;
* a supplied Majorana zero-mode gate;
* QFT/SUSY/topological protection laws.

All spectral and analytic claims remain outside this data carrier as explicit
theorem inputs.
-/
@[socket_debt_tag]
structure ZeroModeProtectionPacket
    (CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout : Type) where
  /-- Defect-free Lee--Yang/large-deviation limit packet. -/
  defectFreeLimit :
    DefectFreeLimitPacket CompletedXiReadout

  /-- Supplied Majorana zero-mode interpretation gate. -/
  majoranaZeroMode :
    MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout

  /-- Extra readout for topological protection data. -/
  protectionReadout :
    ProtectionReadout

namespace ZeroModeProtectionPacket

variable {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout : Type}
variable
  (P : ZeroModeProtectionPacket
    CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout)

end ZeroModeProtectionPacket

end InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
