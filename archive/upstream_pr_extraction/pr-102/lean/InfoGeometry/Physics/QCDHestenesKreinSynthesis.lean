import Mathlib
import InfoGeometry.Physics.QCDHestenesRealColorRepresentation
import InfoGeometry.Physics.QCDHestenesKreinFockPhaseBridge
import InfoGeometry.Physics.QCDHestenesKreinInterfaces
import InfoGeometry.Physics.QCDZornCl55FureyBridge

/-!
# Hestenes--Krein parallel synthesis for the QCD colour/Furey corridor

The purpose of this capstone is to keep the real formulation primary:

* the three-colour representation is realified with an internal `J` satisfying
  `J^2=-I`;
* the representation commutes with that internal complex structure;
* real conjugation is an involution and anticommutes with `J`;
* the real `Cl(5,5)` Fock envelope already owns a Hestenes phase squaring to
  `-I`;
* the existing real Zorn-to-`Cl(5,5)` Furey carrier injection remains available.

No theorem here identifies the colour `J` with the Fock Hestenes phase, nor does
it assert the missing `SU(3)`-equivariant Furey intertwiner.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDHestenesKreinSynthesis

open InfoGeometry.Physics.QCDHestenesRealColorRepresentation
open InfoGeometry.Physics.QCDHestenesKreinFockPhaseBridge
open InfoGeometry.Physics.QCDHestenesKreinInterfaces
open InfoGeometry.Physics.QCDZornCl55FureyBridge

/-- The real colour carrier with its internal Hestenes complex structure. -/
def realColorInternalComplex : InternalComplexCarrier RealColorLane where
  J := realColorJ
  J_sq := realColorJ_sq

/-- The real Hestenes route already provides the algebraic prerequisites for an
internal-complex intertwiner: a square-minus-one colour structure and a
square-minus-one Fock phase.  Constructing the actual carrier map commuting with
both remains separate representation debt. -/
theorem internal_complex_prerequisites_packet :
    realColorInternalComplex.J * realColorInternalComplex.J =
        -(1 : Module.End ℝ RealColorLane) ∧
    fockJ * fockJ = -(1 : FockMat) := by
  exact ⟨realColorJ_sq, fockJ_sq⟩

end InfoGeometry.Physics.QCDHestenesKreinSynthesis

end noncomputable section
