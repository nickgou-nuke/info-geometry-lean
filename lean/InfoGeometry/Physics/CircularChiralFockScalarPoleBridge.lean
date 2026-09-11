import InfoGeometry.Physics.CircularChiralRightRegularCARFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Clifford.Cl55ZornCARComparison

/-!
# Scalar pole transport to the Fock chiral projectors

The scalar circular endpoints are represented by the native complementary
chirality projectors.  This is a relation-level transport statement; it does
not assert an algebra hom from the nonassociative Zorn carrier.
-/

namespace InfoGeometry.Physics.CircularChiralFockScalarPoleBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.CircularChiralRightRegularCARFrame
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison

noncomputable section

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

def positiveFockRail (i : Fin 3) : FockOp :=
  f (firstThreeIndex i)

def negativeFockRail (i : Fin 3) : FockOp :=
  e (firstThreeIndex i)

def circularFockScalarPlus : FockOp := PPlus
def circularFockScalarMinus : FockOp := PMinus

@[simp] theorem circularFockScalarPlus_sq :
    circularFockScalarPlus * circularFockScalarPlus = circularFockScalarPlus := by
  exact PPlus_sq

@[simp] theorem circularFockScalarMinus_sq :
    circularFockScalarMinus * circularFockScalarMinus = circularFockScalarMinus := by
  exact PMinus_sq

theorem circularFockScalarPlus_mul_minus :
    circularFockScalarPlus * circularFockScalarMinus = 0 := by
  exact PPlus_mul_PMinus

theorem circularFockScalarPlus_add_minus :
    circularFockScalarPlus + circularFockScalarMinus = (1 : FockOp) := by
  exact P_sum

def circularFullFockPacket : ChiralSigmaOperatorPacket FockOp where
  uPlus := circularFockScalarPlus
  uMinus := circularFockScalarMinus
  sigmaPlus := positiveFockRail
  sigmaMinus := negativeFockRail

theorem circularFullFockPacket_scalar_laws :
    circularFullFockPacket.uPlus * circularFullFockPacket.uPlus =
        circularFullFockPacket.uPlus ∧
      circularFullFockPacket.uMinus * circularFullFockPacket.uMinus =
        circularFullFockPacket.uMinus ∧
      circularFullFockPacket.uPlus * circularFullFockPacket.uMinus = 0 ∧
      circularFullFockPacket.uPlus + circularFullFockPacket.uMinus =
        (1 : FockOp) := by
  exact ⟨circularFockScalarPlus_sq, circularFockScalarMinus_sq,
    circularFockScalarPlus_mul_minus, circularFockScalarPlus_add_minus⟩

end
end InfoGeometry.Physics.CircularChiralFockScalarPoleBridge
