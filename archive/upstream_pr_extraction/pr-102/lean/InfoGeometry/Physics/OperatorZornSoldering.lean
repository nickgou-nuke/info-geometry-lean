import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Soldering an eight-coordinate chiral packet to the associative shell

The packet retains the two scalar channels and two `Fin 3` rails.  A supplied
soldering map turns each rail into one operator entry; the resulting shell is
the existing transported matrix algebra.  No Zorn multiplication is defined.
-/

namespace InfoGeometry.Physics

variable {Op A : Type*}
variable [Ring A] [StarRing A]

structure ChiralSigmaOperatorPacket (Op : Type*) where
  uPlus : Op
  uMinus : Op
  sigmaPlus : Fin 3 → Op
  sigmaMinus : Fin 3 → Op

structure ChiralSigmaSoldering (Op A : Type*) where
  plus : (Fin 3 → Op) → A
  minus : (Fin 3 → Op) → A

def ChiralSigmaSoldering.toOperatorZornMatrix
    (S : ChiralSigmaSoldering Op A)
    (Q : ChiralSigmaOperatorPacket Op) : OperatorZornMatrix A where
  n_plus_op := 0
  n_minus_op := 0
  sigma_plus_op := S.plus Q.sigmaPlus
  sigma_minus_op := S.minus Q.sigmaMinus

@[simp] theorem toOperatorZornMatrix_n_plus
    (S : ChiralSigmaSoldering Op A)
    (Q : ChiralSigmaOperatorPacket Op) :
    (S.toOperatorZornMatrix Q).n_plus_op = 0 := rfl

@[simp] theorem toOperatorZornMatrix_n_minus
    (S : ChiralSigmaSoldering Op A)
    (Q : ChiralSigmaOperatorPacket Op) :
    (S.toOperatorZornMatrix Q).n_minus_op = 0 := rfl

@[simp] theorem toOperatorZornMatrix_sigma_plus
    (S : ChiralSigmaSoldering Op A)
    (Q : ChiralSigmaOperatorPacket Op) :
    (S.toOperatorZornMatrix Q).sigma_plus_op = S.plus Q.sigmaPlus := rfl

@[simp] theorem toOperatorZornMatrix_sigma_minus
    (S : ChiralSigmaSoldering Op A)
    (Q : ChiralSigmaOperatorPacket Op) :
    (S.toOperatorZornMatrix Q).sigma_minus_op = S.minus Q.sigmaMinus := rfl

theorem toOperatorZornMatrix_toMatrix
    (S : ChiralSigmaSoldering Op A)
    (Q : ChiralSigmaOperatorPacket Op) :
    OperatorZornMatrix.toMatrix (S.toOperatorZornMatrix Q) =
      !![0, S.plus Q.sigmaPlus; S.minus Q.sigmaMinus, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end InfoGeometry.Physics
