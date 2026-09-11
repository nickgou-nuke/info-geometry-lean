import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Sparse chiral operators over a noncommutative coefficient ring

This file is an adapter over the existing operator-valued Zorn owner.  It
does not introduce a second Zorn carrier or a topology.  The coefficient
ring is allowed to be noncommutative; only the displayed finite coordinate
identities are asserted.
-/

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A]

/-- A vector supported at one colour, with coefficient `a`. -/
def operatorColourUnit (k : Fin 3) (a : A) : OperatorVector A :=
  fun i => if i = k then a else 0

def operatorChiralSigmaPlus (k : Fin 3) (a : A) : OperatorZornMatrix A :=
  sigmaPlus (operatorColourUnit k a)

def operatorChiralSigmaMinus (k : Fin 3) (a : A) : OperatorZornMatrix A :=
  sigmaMinus (operatorColourUnit k a)

theorem operatorDot_colourUnit_same (k : Fin 3) (a b : A) :
    operatorDot (operatorColourUnit k a) (operatorColourUnit k b) = a * b := by
  fin_cases k <;>
    simp [operatorDot, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornDot]

theorem chiralSigmaPlus_mul_chiralSigmaMinus (k : Fin 3) (a b : A) :
    operatorZornMul (operatorChiralSigmaPlus k a) (operatorChiralSigmaMinus k b) =
      nPlus (a * b) := by
  rw [operatorChiralSigmaPlus, operatorChiralSigmaMinus, sigmaPlus_mul_sigmaMinus]
  rw [operatorDot_colourUnit_same]

theorem chiralSigmaMinus_mul_chiralSigmaPlus (k : Fin 3) (a b : A) :
    operatorZornMul (operatorChiralSigmaMinus k a) (operatorChiralSigmaPlus k b) =
      nMinus (a * b) := by
  rw [operatorChiralSigmaMinus, operatorChiralSigmaPlus, sigmaMinus_mul_sigmaPlus]
  rw [operatorDot_colourUnit_same]

theorem chiralPlane_CAR_operator (k : Fin 3) :
    operatorZornMul (operatorChiralSigmaPlus k (1 : A)) (operatorChiralSigmaMinus k 1) =
        nPlus 1 ∧
    operatorZornMul (operatorChiralSigmaMinus k (1 : A)) (operatorChiralSigmaPlus k 1) =
        nMinus 1 := by
  constructor
  · simpa using
      (chiralSigmaPlus_mul_chiralSigmaMinus (A := A) k (1 : A) (1 : A))
  · simpa using
      (chiralSigmaMinus_mul_chiralSigmaPlus (A := A) k (1 : A) (1 : A))

theorem chiralSigmaPlus_mul_chiralSigmaPlus (k l : Fin 3) (a b : A) :
    operatorZornMul (operatorChiralSigmaPlus k a) (operatorChiralSigmaPlus l b) =
      sigmaMinus (operatorCross (operatorColourUnit k a) (operatorColourUnit l b)) := by
  exact sigmaPlus_mul_sigmaPlus _ _

theorem chiralSigmaMinus_mul_chiralSigmaMinus (k l : Fin 3) (a b : A) :
    operatorZornMul (operatorChiralSigmaMinus k a) (operatorChiralSigmaMinus l b) =
      sigmaPlus (-operatorCross (operatorColourUnit k a) (operatorColourUnit l b)) := by
  exact sigmaMinus_mul_sigmaMinus _ _

@[simp] theorem chiralSigmaPlus_zero_mul_one :
    operatorZornMul (operatorChiralSigmaPlus 0 (1 : A))
        (operatorChiralSigmaPlus 1 1) = operatorChiralSigmaMinus 2 1 := by
  rw [chiralSigmaPlus_mul_chiralSigmaPlus]
  congr 1
  funext i
  fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]

@[simp] theorem chiralSigmaPlus_zero_mul_two :
    operatorZornMul (operatorChiralSigmaPlus 0 (1 : A))
        (operatorChiralSigmaPlus 2 1) = operatorChiralSigmaMinus 1 (-1) := by
  rw [chiralSigmaPlus_mul_chiralSigmaPlus]
  congr 1
  funext i
  fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]

@[simp] theorem chiralSigmaPlus_one_mul_zero :
    operatorZornMul (operatorChiralSigmaPlus 1 (1 : A))
        (operatorChiralSigmaPlus 0 1) = operatorChiralSigmaMinus 2 (-1) := by
  rw [chiralSigmaPlus_mul_chiralSigmaPlus]
  congr 1
  funext i
  fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]

@[simp] theorem chiralSigmaPlus_one_mul_two :
    operatorZornMul (operatorChiralSigmaPlus 1 (1 : A))
        (operatorChiralSigmaPlus 2 1) = operatorChiralSigmaMinus 0 1 := by
  rw [chiralSigmaPlus_mul_chiralSigmaPlus]
  congr 1
  funext i
  fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]

@[simp] theorem chiralSigmaPlus_two_mul_zero :
    operatorZornMul (operatorChiralSigmaPlus 2 (1 : A))
        (operatorChiralSigmaPlus 0 1) = operatorChiralSigmaMinus 1 1 := by
  rw [chiralSigmaPlus_mul_chiralSigmaPlus]
  congr 1
  funext i
  fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]

@[simp] theorem chiralSigmaPlus_two_mul_one :
    operatorZornMul (operatorChiralSigmaPlus 2 (1 : A))
        (operatorChiralSigmaPlus 1 1) = operatorChiralSigmaMinus 0 (-1) := by
  rw [chiralSigmaPlus_mul_chiralSigmaPlus]
  congr 1
  funext i
  fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]

end InfoGeometry.Canonical
