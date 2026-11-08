import InfoGeometry.Optics.OperatorCausalSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Four-vector to operator-Zorn coordinate readout

This is a coordinate bridge only.  It does not identify a four-vector with a
non-associative Zorn algebra, and it keeps the coefficient ring explicit.
-/

namespace InfoGeometry.Physics.OperatorFourVectorZornReadout

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

variable {A : Type*} [Ring A] [StarRing A]

def fromCoordinates (v : Fin 4 → A) : OperatorZornMatrix A where
  n_plus_op := v 0 + v 3
  n_minus_op := v 0 - v 3
  sigma_plus_op := v 1 - v 2
  sigma_minus_op := v 1 + v 2

def fromCoordinatesRotor (v : Fin 4 → A) (rotor : A) : OperatorZornMatrix A where
  n_plus_op := v 0 + v 3
  n_minus_op := v 0 - v 3
  sigma_plus_op := v 1 - rotor * v 2
  sigma_minus_op := v 1 + rotor * v 2

@[simp] theorem fromCoordinates_n_plus (v : Fin 4 → A) :
    (fromCoordinates v).n_plus_op = v 0 + v 3 := rfl

@[simp] theorem fromCoordinates_n_minus (v : Fin 4 → A) :
    (fromCoordinates v).n_minus_op = v 0 - v 3 := rfl

@[simp] theorem fromCoordinates_sigma_plus (v : Fin 4 → A) :
    (fromCoordinates v).sigma_plus_op = v 1 - v 2 := rfl

@[simp] theorem fromCoordinates_sigma_minus (v : Fin 4 → A) :
    (fromCoordinates v).sigma_minus_op = v 1 + v 2 := rfl

theorem fromCoordinates_toMatrix (v : Fin 4 → A) :
    OperatorZornMatrix.toMatrix (fromCoordinates v) =
      !![v 0 + v 3, v 1 - v 2;
         v 1 + v 2, v 0 - v 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fromCoordinatesRotor_toMatrix (v : Fin 4 → A) (rotor : A) :
    OperatorZornMatrix.toMatrix (fromCoordinatesRotor v rotor) =
      !![v 0 + v 3, v 1 - rotor * v 2;
         v 1 + rotor * v 2, v 0 - v 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fromCoordinates_diagonal_readout (v : Fin 4 → A) :
    (fromCoordinates v).n_plus_op + (fromCoordinates v).n_minus_op =
      (2 : A) * v 0 := by
  dsimp [fromCoordinates]
  noncomm_ring

theorem fromCoordinates_offDiagonal_sum (v : Fin 4 → A) :
    (fromCoordinates v).sigma_plus_op +
        (fromCoordinates v).sigma_minus_op = (2 : A) * v 1 := by
  dsimp [fromCoordinates]
  noncomm_ring

theorem fromCoordinatesRotor_diagonal_sum (v : Fin 4 → A) (rotor : A) :
    (fromCoordinatesRotor v rotor).n_plus_op +
        (fromCoordinatesRotor v rotor).n_minus_op = (2 : A) * v 0 := by
  dsimp [fromCoordinatesRotor]
  noncomm_ring

theorem fromCoordinatesRotor_offDiagonal_sum (v : Fin 4 → A) (rotor : A) :
    (fromCoordinatesRotor v rotor).sigma_plus_op +
        (fromCoordinatesRotor v rotor).sigma_minus_op = (2 : A) * v 1 := by
  dsimp [fromCoordinatesRotor]
  noncomm_ring

theorem fromCoordinatesRotor_offDiagonal_difference (v : Fin 4 → A) (rotor : A) :
    (fromCoordinatesRotor v rotor).sigma_minus_op -
        (fromCoordinatesRotor v rotor).sigma_plus_op =
      (2 : A) * (rotor * v 2) := by
  dsimp [fromCoordinatesRotor]
  noncomm_ring

end InfoGeometry.Physics.OperatorFourVectorZornReadout
