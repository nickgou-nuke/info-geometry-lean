import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
import InfoGeometry.Canonical.PrimeMertensDefectBoundary
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

Witness-gated zero-mode and topological-protection layer for the prime
Lee--Yang program.

This module records the QFT/SUSY interpretation of the defect-free prime
Lee--Yang limit:

* half-filling / `1/2` as the particle-hole centering law;
* zero-energy Majorana mode data supplied by the arithmetic Majorana gate;
* unbroken SUSY / Witten-cancellation readout supplied as a law;
* topological protection supplied as a law;
* matching between protected zero modes and the completed-`xi` zero readout
  supplied as a law.

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

All spectral and analytic claims remain explicit certificates.
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

  /-- Particle-hole centering / half-filling law. -/
  halfFillingCenter_law : Prop
  halfFillingCenter_certificate :
    halfFillingCenter_law

  /-- Zero-point / zero-energy shift law for the protected lane. -/
  zeroPointShift_law : Prop
  zeroPointShift_certificate :
    zeroPointShift_law

  /-- Unbroken SUSY or Witten-cancellation law. -/
  unbrokenSUSY_law : Prop
  unbrokenSUSY_certificate :
    unbrokenSUSY_law

  /-- Topological protection law for the zero-mode lane. -/
  topologicalProtection_law : Prop
  topologicalProtection_certificate :
    topologicalProtection_law

  /--
  Matching law between protected zero modes and the completed-`xi` zero
  readout.  This is the future spectral theorem, not a consequence of the raw
  Majorana Witten character.
  -/
  protectedZeroModes_eq_completedXiZeros_law : Prop
  protectedZeroModes_eq_completedXiZeros_certificate :
    protectedZeroModes_eq_completedXiZeros_law

  /-- Guardrail: inverse-zeta Witten poles are not directly zero modes. -/
  inverseZetaWitten_not_zeroMode_guard : Type

  /-- Guardrail: this packet is not an unconditional RH proof. -/
  no_unconditional_RH_claim_guard : Type

namespace ZeroModeProtectionPacket

variable {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout : Type}
variable
  (P : ZeroModeProtectionPacket
    CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout)

/-- Re-export of the supplied half-filling / particle-hole centering law. -/
theorem halfFillingCenter :
    P.halfFillingCenter_law :=
  P.halfFillingCenter_certificate

/-- Re-export of the supplied zero-point / zero-energy shift law. -/
theorem zeroPointShift :
    P.zeroPointShift_law :=
  P.zeroPointShift_certificate

/-- Re-export of the supplied unbroken-SUSY/Witten-cancellation law. -/
theorem unbrokenSUSY :
    P.unbrokenSUSY_law :=
  P.unbrokenSUSY_certificate

/-- Re-export of the supplied topological-protection law. -/
theorem topologicalProtection :
    P.topologicalProtection_law :=
  P.topologicalProtection_certificate

/-- Re-export of the supplied protected-zero-mode/completed-`xi` matching law. -/
theorem protectedZeroModes_eq_completedXiZeros :
    P.protectedZeroModes_eq_completedXiZeros_law :=
  P.protectedZeroModes_eq_completedXiZeros_certificate

/-- The packet contains the supplied Majorana zero-energy law. -/
theorem majorana_zero_energy :
    P.majoranaZeroMode.zero_energy_law :=
  P.majoranaZeroMode.zero_energy

/-- The packet contains the supplied Majorana zero-readout comparison law. -/
theorem majorana_zero_readout_comparison :
    P.majoranaZeroMode.zero_readout_comparison_law :=
  P.majoranaZeroMode.zero_readout_comparison

/-- The packet contains the defect-free critical-line zero-location reduction law. -/
theorem defectFreeLimit_implies_criticalLineZeros :
    P.defectFreeLimit.defectFreeLimit_implies_criticalLineZeros_law :=
  P.defectFreeLimit.defectFreeLimit_implies_criticalLineZeros

end ZeroModeProtectionPacket

/--
Bridge data needed to build a zero-mode protection packet from a defect-free
Lee--Yang limit and a Majorana zero-mode gate.
-/
@[socket_debt_tag]
structure ZeroModeProtectionBridge
    (ProtectionReadout : Type) where
  protectionReadout : ProtectionReadout
  halfFillingCenter_law : Prop
  halfFillingCenter_certificate :
    halfFillingCenter_law
  zeroPointShift_law : Prop
  zeroPointShift_certificate :
    zeroPointShift_law
  unbrokenSUSY_law : Prop
  unbrokenSUSY_certificate :
    unbrokenSUSY_law
  topologicalProtection_law : Prop
  topologicalProtection_certificate :
    topologicalProtection_law
  protectedZeroModes_eq_completedXiZeros_law : Prop
  protectedZeroModes_eq_completedXiZeros_certificate :
    protectedZeroModes_eq_completedXiZeros_law
  inverseZetaWitten_not_zeroMode_guard : Type
  no_unconditional_RH_claim_guard : Type

/--
Assemble the protected zero-mode packet from existing defect-free and Majorana
zero-mode witnesses plus the supplied QFT/SUSY protection bridge.
-/
def zeroModeProtection_of_defectFreeLimit
    {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout : Type}
    (D : DefectFreeLimitPacket CompletedXiReadout)
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout)
    (B : ZeroModeProtectionBridge ProtectionReadout) :
    ZeroModeProtectionPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout where
  defectFreeLimit := D
  majoranaZeroMode := G
  protectionReadout := B.protectionReadout
  halfFillingCenter_law := B.halfFillingCenter_law
  halfFillingCenter_certificate := B.halfFillingCenter_certificate
  zeroPointShift_law := B.zeroPointShift_law
  zeroPointShift_certificate := B.zeroPointShift_certificate
  unbrokenSUSY_law := B.unbrokenSUSY_law
  unbrokenSUSY_certificate := B.unbrokenSUSY_certificate
  topologicalProtection_law := B.topologicalProtection_law
  topologicalProtection_certificate := B.topologicalProtection_certificate
  protectedZeroModes_eq_completedXiZeros_law :=
    B.protectedZeroModes_eq_completedXiZeros_law
  protectedZeroModes_eq_completedXiZeros_certificate :=
    B.protectedZeroModes_eq_completedXiZeros_certificate
  inverseZetaWitten_not_zeroMode_guard :=
    B.inverseZetaWitten_not_zeroMode_guard
  no_unconditional_RH_claim_guard :=
    B.no_unconditional_RH_claim_guard

/-- Owner theorem: the assembled packet re-exports its supplied protection laws. -/
theorem zeroModeProtection_of_defectFreeLimit_reexports
    {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout : Type}
    (D : DefectFreeLimitPacket CompletedXiReadout)
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout)
    (B : ZeroModeProtectionBridge ProtectionReadout) :
      (zeroModeProtection_of_defectFreeLimit D G B).halfFillingCenter_law ∧
      (zeroModeProtection_of_defectFreeLimit D G B).zeroPointShift_law ∧
      (zeroModeProtection_of_defectFreeLimit D G B).unbrokenSUSY_law ∧
      (zeroModeProtection_of_defectFreeLimit D G B).topologicalProtection_law ∧
      (zeroModeProtection_of_defectFreeLimit D G B).protectedZeroModes_eq_completedXiZeros_law := by
  exact ⟨
    (zeroModeProtection_of_defectFreeLimit D G B).halfFillingCenter,
    (zeroModeProtection_of_defectFreeLimit D G B).zeroPointShift,
    (zeroModeProtection_of_defectFreeLimit D G B).unbrokenSUSY,
    (zeroModeProtection_of_defectFreeLimit D G B).topologicalProtection,
    (zeroModeProtection_of_defectFreeLimit D G B).protectedZeroModes_eq_completedXiZeros⟩

end InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
