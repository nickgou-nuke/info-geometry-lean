import InfoGeometry.Physics.CircularChiralFockScalarPoleBridge
import InfoGeometry.Physics.OperatorZornSoldering
import InfoGeometry.Algebra.CircularChiralOperatorEightBridge

/-!
# Full circular/Fock operator-Zorn packet

This is the local, pinned-Mathlib realization of the updated PR #100 edge.
The two scalar circular endpoints are the native Fock chirality projectors;
the six off-diagonal channels are the three-mode CAR rails.  No
nonassociative-to-associative algebra homomorphism is asserted.
-/

namespace InfoGeometry.Physics.CircularChiralFockOperatorZornBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.CircularChiralFockScalarPoleBridge
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Algebra.CircularChiralOperatorEightBridge

noncomputable section

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

def circularFockPacket : ChiralSigmaOperatorPacket FockOp where
  uPlus := circularFockScalarPlus
  uMinus := circularFockScalarMinus
  sigmaPlus := positiveFockRail
  sigmaMinus := negativeFockRail

def fockPoleProjector (i : Fin 2) : FockOp :=
  if i = 0 then circularFockScalarMinus else circularFockScalarPlus

theorem fockPoleProjector_zero :
    fockPoleProjector 0 = circularFockScalarMinus := by
  simp [fockPoleProjector]

theorem fockPoleProjector_one :
    fockPoleProjector 1 = circularFockScalarPlus := by
  simp [fockPoleProjector]

theorem circularFockPacket_scalar_laws :
    circularFockPacket.uPlus * circularFockPacket.uPlus = circularFockPacket.uPlus ∧
      circularFockPacket.uMinus * circularFockPacket.uMinus = circularFockPacket.uMinus ∧
      circularFockPacket.uPlus * circularFockPacket.uMinus = 0 ∧
      circularFockPacket.uPlus + circularFockPacket.uMinus = (1 : FockOp) := by
  exact circularFullFockPacket_scalar_laws

def colourSoldering (c : Fin 3) : ChiralSigmaSoldering FockOp FockOp where
  plus := fun q => q c
  minus := fun q => q c

def circularColourOperatorZorn (c : Fin 3) : OperatorZornMatrix FockOp where
  n_plus_op := circularFockScalarPlus
  n_minus_op := circularFockScalarMinus
  sigma_plus_op := positiveFockRail c
  sigma_minus_op := negativeFockRail c

theorem circularColourOperatorZorn_toMatrix (c : Fin 3) :
    OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) =
      !![circularFockScalarPlus, positiveFockRail c;
         negativeFockRail c, circularFockScalarMinus] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem circular_chiral_fock_operatorZorn_packet (c : Fin 3) :
    circularFockScalarPlus * circularFockScalarPlus = circularFockScalarPlus ∧
    circularFockScalarMinus * circularFockScalarMinus = circularFockScalarMinus ∧
    circularFockScalarPlus * circularFockScalarMinus = 0 ∧
    circularFockScalarPlus + circularFockScalarMinus = (1 : FockOp) ∧
    positiveFockRail c * positiveFockRail c = 0 ∧
    negativeFockRail c * negativeFockRail c = 0 ∧
    positiveFockRail c * negativeFockRail c +
      negativeFockRail c * positiveFockRail c = (1 : FockOp) ∧
    OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) =
      !![circularFockScalarPlus, positiveFockRail c;
         negativeFockRail c, circularFockScalarMinus] := by
  exact ⟨circularFockScalarPlus_sq, circularFockScalarMinus_sq,
    circularFockScalarPlus_mul_minus, circularFockScalarPlus_add_minus,
    f_sq (firstThreeIndex c), e_sq (firstThreeIndex c),
    by simpa [positiveFockRail, negativeFockRail, add_comm] using
      (ef_car (firstThreeIndex c) (firstThreeIndex c)),
    circularColourOperatorZorn_toMatrix c⟩

end
end InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
