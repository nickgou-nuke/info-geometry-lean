import InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.CircularChiralBivectorRotorBridge

namespace InfoGeometry.Physics.CircularOperatorPotentialNativeBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
open InfoGeometry.Physics.CircularChiralBivectorRotorBridge
open InfoGeometry.Physics.Cl55SpinorCartanFock

noncomputable section

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

def circularEvenPotential (aPlus aMinus : FockOp) : ChiralSigmaOperatorPacket FockOp :=
  { uPlus := aPlus, uMinus := aMinus
    sigmaPlus := fun _ => 0, sigmaMinus := fun _ => 0 }

def circularOddPotential
    (upper lower : Fin 3 → FockOp) : ChiralSigmaOperatorPacket FockOp :=
  { uPlus := 0, uMinus := 0, sigmaPlus := upper, sigmaMinus := lower }

def circularOperatorPotential : ChiralSigmaOperatorPacket FockOp :=
  circularFockPacket

theorem circularOperatorPotential_scalar_packet :
    circularOperatorPotential.uPlus = CircularChiralFockScalarPoleBridge.circularFockScalarPlus ∧
      circularOperatorPotential.uMinus = CircularChiralFockScalarPoleBridge.circularFockScalarMinus := by
  simp [circularOperatorPotential, circularFockPacket]

theorem circularOperatorPotential_odd_packet (i : Fin 3) :
    circularOperatorPotential.sigmaPlus i = CircularChiralFockScalarPoleBridge.positiveFockRail i ∧
      circularOperatorPotential.sigmaMinus i = CircularChiralFockScalarPoleBridge.negativeFockRail i := by
  simp [circularOperatorPotential, circularFockPacket]

theorem circularOperatorPotential_even_odd_decomposition (i : Fin 3) :
    circularOperatorPotential.uPlus = CircularChiralFockScalarPoleBridge.circularFockScalarPlus ∧
      circularOperatorPotential.uMinus = CircularChiralFockScalarPoleBridge.circularFockScalarMinus ∧
      circularOperatorPotential.sigmaPlus i = CircularChiralFockScalarPoleBridge.positiveFockRail i ∧
      circularOperatorPotential.sigmaMinus i = CircularChiralFockScalarPoleBridge.negativeFockRail i := by
  simp [circularOperatorPotential, circularFockPacket]

theorem circularOperatorPotential_scalar_projector_packet :
    circularOperatorPotential.uPlus * circularOperatorPotential.uPlus =
        circularOperatorPotential.uPlus ∧
      circularOperatorPotential.uMinus * circularOperatorPotential.uMinus =
        circularOperatorPotential.uMinus ∧
      circularOperatorPotential.uPlus * circularOperatorPotential.uMinus = 0 ∧
      circularOperatorPotential.uPlus + circularOperatorPotential.uMinus =
        (1 : FockOp) := by
  exact circularFockPacket_scalar_laws

theorem bivectorPhase_sq :
    bivectorRotor * bivectorRotor = -(1 : RotorCarrier) :=
  bivectorRotor_sq

end
end InfoGeometry.Physics.CircularOperatorPotentialNativeBridge
