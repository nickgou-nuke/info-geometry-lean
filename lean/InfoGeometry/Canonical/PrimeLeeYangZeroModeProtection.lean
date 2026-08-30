import InfoGeometry.Canonical.PrimeMertensDefectBoundary

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

open InfoGeometry.Canonical.PrimeMertensDefectBoundary

/-! ## Defect-free zero-mode readout packet -/

/--
The theorem-safe zero-mode protection packet for the prime Lee--Yang lane.

This is exactly the existing defect-free bridge data: a finite Lee--Yang
approximation together with the supplied large-deviation witness needed to read
the defect-free limit.  It stores no arbitrary SUSY, RH, or completed-`xi`
zero-identification proposition fields.
-/
abbrev ZeroModeProtectionPacket (CompletedXiReadout : Type) : Type (u+1) :=
  MertensToDefectFreeBridge CompletedXiReadout

end PrimeLeeYangZeroModeProtection
