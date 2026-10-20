/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Holography.PlabicKreinTwistedClusterMutation

/-!
# Matrix representation of the local Plabic/Krein carrier

The local `Cl11Op` carrier is an explicit four-coordinate algebra.  This file
gives its genuine `2 × 2` matrix representation and proves the algebra laws
needed to transport the local mutation identities.  It does not identify a
general plabic square move with a matrix conjugation.
-/

namespace InfoGeometry.Holography.PlabicKrein

namespace Cl11Op

variable {R : Type*} [CommRing R]

/-- The canonical matrix representation of a local `Cl11Op`. -/
def toMatrix (A : Cl11Op R) : Matrix (Fin 2) (Fin 2) R :=
  !![A.m11, A.m12; A.m21, A.m22]

omit [CommRing R] in
theorem toMatrix_injective :
    Function.Injective (toMatrix : Cl11Op R → Matrix (Fin 2) (Fin 2) R) := by
  intro A B h
  apply Cl11Op.ext
  · simpa [toMatrix] using congrFun (congrFun h 0) 0
  · simpa [toMatrix] using congrFun (congrFun h 0) 1
  · simpa [toMatrix] using congrFun (congrFun h 1) 0
  · simpa [toMatrix] using congrFun (congrFun h 1) 1

theorem toMatrix_zero : toMatrix (zero : Cl11Op R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_one : toMatrix (one : Cl11Op R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, one]

/-- Matrix representatives of the black projector and upper nilpotent edge. -/
def matrixBlack : Matrix (Fin 2) (Fin 2) R :=
  toMatrix (nodeBlack (1 : R))

def matrixEdge : Matrix (Fin 2) (Fin 2) R :=
  toMatrix (edgeTwist (1 : R))

/-- The matrix realization exposes explicit noncommutativity over a
nontrivial coefficient ring. -/
theorem matrixBlack_mul_edge_ne [Nontrivial R] :
    matrixBlack (R := R) * matrixEdge (R := R) ≠
      matrixEdge (R := R) * matrixBlack (R := R) := by
  intro h
  have hentry := congrFun (congrFun h 0) 1
  simpa [matrixBlack, matrixEdge, toMatrix, mul, nodeBlack, edgeTwist,
    Matrix.mul_apply,
    Fin.sum_univ_two] using hentry

theorem toMatrix_add (A B : Cl11Op R) :
    toMatrix (add A B) = toMatrix A + toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_mul (A B : Cl11Op R) :
    toMatrix (mul A B) = toMatrix A * toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem toMatrix_mutationRotor (w : R) :
    toMatrix (mutationRotor w) = 1 + toMatrix (edgeTwist w) := by
  rw [mutationRotor]
  rw [toMatrix_add, toMatrix_one]

theorem matrix_mutation_rotor_unitary (w : R) :
    toMatrix (mutationRotor w) * toMatrix (mutationRotorInv w) = 1 ∧
      toMatrix (mutationRotorInv w) * toMatrix (mutationRotor w) = 1 := by
  constructor
  · rw [← toMatrix_mul, mutation_rotor_unitary w |>.1, toMatrix_one]
  · rw [← toMatrix_mul, mutation_rotor_unitary w |>.2, toMatrix_one]

theorem matrix_cluster_mutation_is_exponential_adjoint (x w : R) :
    toMatrix (mul (mul (mutationRotor w) (nodeBlack x)) (mutationRotorInv w)) =
      toMatrix ⟨x, -(x * w), 0, 0⟩ := by
  rw [cluster_mutation_is_exponential_adjoint]

end Cl11Op

end InfoGeometry.Holography.PlabicKrein
