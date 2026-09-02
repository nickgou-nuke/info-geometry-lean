import InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
import InfoGeometry.Physics.OperatorFourVectorZornReadout

/-!
# Circular operator potential

The potential is an `OperatorZornMatrix` built from an existing chiral packet.
This is a readout/constructor, not a replacement carrier and not an algebra
homomorphism from the non-associative Zorn algebra.
-/

namespace InfoGeometry.Physics.CircularOperatorPotential

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

variable {A : Type*} [Ring A] [StarRing A]

def fromPacket (Q : ChiralSigmaOperatorPacket A)
    (aPlus aMinus : A) (i : Fin 3) : OperatorZornMatrix A where
  n_plus_op := aPlus * Q.uPlus
  n_minus_op := aMinus * Q.uMinus
  sigma_plus_op := Q.sigmaPlus i
  sigma_minus_op := Q.sigmaMinus i

theorem fromPacket_toMatrix (Q : ChiralSigmaOperatorPacket A)
    (aPlus aMinus : A) (i : Fin 3) :
    OperatorZornMatrix.toMatrix (fromPacket Q aPlus aMinus i) =
      !![aPlus * Q.uPlus, Q.sigmaPlus i;
         Q.sigmaMinus i, aMinus * Q.uMinus] := by
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

theorem fromPacket_slots (Q : ChiralSigmaOperatorPacket A)
    (aPlus aMinus : A) (i : Fin 3) :
    (fromPacket Q aPlus aMinus i).n_plus_op = aPlus * Q.uPlus ∧
    (fromPacket Q aPlus aMinus i).n_minus_op = aMinus * Q.uMinus ∧
    (fromPacket Q aPlus aMinus i).sigma_plus_op = Q.sigmaPlus i ∧
    (fromPacket Q aPlus aMinus i).sigma_minus_op = Q.sigmaMinus i := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end InfoGeometry.Physics.CircularOperatorPotential
