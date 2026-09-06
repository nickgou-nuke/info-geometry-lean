import InfoGeometry.Algebra.EulerLaurentDerivation
import InfoGeometry.Topology.AlgebraicPunctureDeRham
import InfoGeometry.Topology.ZeroMultiplicityResidueBridge

/-!
# Analytic zero multiplicity to finite divisor charge

This is a comparison bridge only.  The finite divisor and residue calculus
does not depend on analytic functions; this file records how an already
supplied analytic multiplicity datum is encoded by the native signed integer
order packet.
-/

noncomputable section

namespace InfoGeometry.Topology.ZeroMultiplicityFiniteDivisorBridge

open InfoGeometry.Algebra.EulerLaurentDerivation
open InfoGeometry.Topology.AlgebraicPunctureDeRham
open InfoGeometry.Topology.ZeroMultiplicityResidueBridge

/-- Encode a supplied positive analytic zero multiplicity as a finite zero
    divisor packet.  The unit component is intentionally irrelevant to the
    charge and is set to zero. -/
def divisorPacketOfZero (d : LocalZeroDatum) : LocalDivisorData ℤ where
  order := d.multiplicity
  unit := 0

theorem divisorPacketOfZero_isZero (d : LocalZeroDatum) :
    isZero (divisorPacketOfZero d) := by
  change 0 < (d.multiplicity : ℤ)
  exact_mod_cast d.m_pos

theorem divisorPacketOfZero_order (d : LocalZeroDatum) :
    (divisorPacketOfZero d).order = (d.multiplicity : ℤ) :=
  rfl

/-- The native algebraic residue, after scalar extension, agrees with the
    supplied logarithmic-derivative residue coefficient. -/
theorem complex_residue_charge_eq_logDerivResidue (d : LocalZeroDatum) :
    ((residue (chargeForm (divisorPacketOfZero d)) : ℤ) : ℂ) =
      logDerivResidue d := by
  rw [residue_chargeForm]
  simp [divisorPacketOfZero, logDerivResidue]

/-- The von Mangoldt sign convention is the negative of the same native
    divisor charge. -/
theorem complex_residue_charge_eq_neg_vonMangoldtResidue
    (d : LocalZeroDatum) :
    -((residue (chargeForm (divisorPacketOfZero d)) : ℤ) : ℂ) =
      vonMangoldtChannelResidue d := by
  rw [residue_chargeForm]
  simp [divisorPacketOfZero, vonMangoldtChannelResidue]

end InfoGeometry.Topology.ZeroMultiplicityFiniteDivisorBridge

end
