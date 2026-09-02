import InfoGeometry.Physics.CircularOperatorFourPotentialRotorReadout
import InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis

/-! The canonical packaging of the circular potential is the existing chiral
operator packet.  Its even/odd split is structural; the four-coordinate
matrix is only a readout of this packet. -/
namespace InfoGeometry.Physics.CircularParaKahlerSuperpotentialBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
open InfoGeometry.Physics.CircularChiralFockScalarPoleBridge
open InfoGeometry.Physics.CircularOperatorFourPotentialRotorReadout

noncomputable section
abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5
abbrev CircularOperatorSuperpotential := ChiralSigmaOperatorPacket FockOp

def circularSuperpotential : CircularOperatorSuperpotential := circularFockPacket

def evenSector (W : CircularOperatorSuperpotential) : CircularOperatorSuperpotential :=
  { uPlus := W.uPlus, uMinus := W.uMinus
    sigmaPlus := fun _ => 0, sigmaMinus := fun _ => 0 }

def oddSector (W : CircularOperatorSuperpotential) : CircularOperatorSuperpotential :=
  { uPlus := 0, uMinus := 0
    sigmaPlus := W.sigmaPlus, sigmaMinus := W.sigmaMinus }

def packetAdd (W V : CircularOperatorSuperpotential) : CircularOperatorSuperpotential :=
  { uPlus := W.uPlus + V.uPlus, uMinus := W.uMinus + V.uMinus
    sigmaPlus := fun i => W.sigmaPlus i + V.sigmaPlus i
    sigmaMinus := fun i => W.sigmaMinus i + V.sigmaMinus i }

theorem superpotential_even_odd_reconstruction (W : CircularOperatorSuperpotential) :
  W = packetAdd (evenSector W) (oddSector W) := by
  cases W
  simp [packetAdd, evenSector, oddSector]

theorem circularSuperpotential_scalar_packet :
    circularSuperpotential.uPlus = circularFockScalarPlus ∧
      circularSuperpotential.uMinus = circularFockScalarMinus := by
  exact ⟨rfl, rfl⟩

theorem circularSuperpotential_odd_packet (i : Fin 3) :
    circularSuperpotential.sigmaPlus i = positiveFockRail i ∧
      circularSuperpotential.sigmaMinus i = negativeFockRail i := by
  exact ⟨rfl, rfl⟩

theorem circularSuperpotential_four_readout (i : Fin 3) :
    realSplitFourSoldering (circularCompressedFourPotential i) =
      OperatorZornMatrix.toMatrix (circularColourOperatorZorn i) :=
  realSplitFourSoldering_eq_circularOperatorZorn i

theorem circularSuperpotential_1331_packet (i : Fin 3) :
    circularSuperpotential.uPlus = circularFockScalarPlus ∧
      circularSuperpotential.sigmaPlus i = positiveFockRail i ∧
      circularSuperpotential.sigmaMinus i = negativeFockRail i ∧
      circularSuperpotential.uMinus = circularFockScalarMinus ∧
      (circularSuperpotential = packetAdd (evenSector circularSuperpotential)
        (oddSector circularSuperpotential)) := by
  exact ⟨rfl, rfl, rfl, rfl,
    superpotential_even_odd_reconstruction circularSuperpotential⟩

end
end InfoGeometry.Physics.CircularParaKahlerSuperpotentialBridge
