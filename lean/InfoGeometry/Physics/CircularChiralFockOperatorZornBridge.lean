import Mathlib.Tactic
import InfoGeometry.Algebra.CircularChiralOperatorEightBridge
import InfoGeometry.Clifford.Cl55ZornCARComparison
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.CircularChiralFockScalarPoleBridge
import InfoGeometry.Physics.OperatorZornSoldering
import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Projective.FiveGradedCentralizer

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

/-- Native second-quantized readout of a positive circular/root-plus channel. -/
def positiveRailFock (i : Fin 3) : FockOp :=
  InfoGeometry.Physics.Cl55SpinorCartanFock.f (firstThreeIndex i)

/-- Native second-quantized readout of a negative circular/root-minus channel. -/
def negativeRailFock (i : Fin 3) : FockOp :=
  InfoGeometry.Physics.Cl55SpinorCartanFock.e (firstThreeIndex i)

/-! The PR #87/#100 convention is recorded explicitly here: in this Fock
realization the positive circular rail is the annihilation rail `f`, while
the negative circular rail is the creation rail `e`.  Keeping these names
distinct from the exterior/right-regular convention prevents an accidental
identification of the two particle--hole orientations. -/

@[simp] theorem positiveRailFock_eq_positiveFockRail (i : Fin 3) :
    positiveRailFock i = positiveFockRail i :=
  rfl

@[simp] theorem negativeRailFock_eq_negativeFockRail (i : Fin 3) :
    negativeRailFock i = negativeFockRail i :=
  rfl

@[simp] theorem positiveRailFock_sq (i : Fin 3) :
    positiveRailFock i * positiveRailFock i = 0 := by
  exact f_sq (firstThreeIndex i)

@[simp] theorem negativeRailFock_sq (i : Fin 3) :
    negativeRailFock i * negativeRailFock i = 0 := by
  exact e_sq (firstThreeIndex i)

theorem positiveRailFock_anticomm (i j : Fin 3) :
    positiveRailFock i * positiveRailFock j +
      positiveRailFock j * positiveRailFock i = 0 := by
  exact f_anticomm (firstThreeIndex i) (firstThreeIndex j)

theorem negativeRailFock_anticomm (i j : Fin 3) :
    negativeRailFock i * negativeRailFock j +
      negativeRailFock j * negativeRailFock i = 0 := by
  exact e_anticomm (firstThreeIndex i) (firstThreeIndex j)

theorem positive_negativeRailFock_CAR (i j : Fin 3) :
    positiveRailFock i * negativeRailFock j +
      negativeRailFock j * positiveRailFock i =
        if i = j then (1 : FockOp) else 0 := by
  have h := ef_car (firstThreeIndex j) (firstThreeIndex i)
  rw [add_comm] at h
  by_cases hij : i = j
  · subst j
    simpa [positiveRailFock, negativeRailFock] using h
  · have hidx : firstThreeIndex j ≠ firstThreeIndex i := by
      intro hji
      exact hij (firstThreeIndex_injective hji.symm)
    simpa [positiveRailFock, negativeRailFock, hij, hidx] using h

def circularFockPacket : ChiralSigmaOperatorPacket FockOp where
  uPlus := circularFockScalarPlus
  uMinus := circularFockScalarMinus
  sigmaPlus := positiveFockRail
  sigmaMinus := negativeFockRail

/-- Indices of the positive and negative circular rails in the ordered
eight-frame. -/
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
