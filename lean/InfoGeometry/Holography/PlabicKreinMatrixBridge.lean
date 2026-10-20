/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Holography.PlabicKreinTwistedClusterMutation
import InfoGeometry.Topology.DirectedPathMonoidTransport

/-!
# Matrix representation of the local Plabic/Krein carrier

The local `Cl11Op` carrier is an explicit four-coordinate algebra.  This file
gives its genuine `2 × 2` matrix representation and proves the algebra laws
needed to transport the local mutation identities.  It does not identify a
general plabic square move with a matrix conjugation.
-/

namespace InfoGeometry.Holography.PlabicKrein

open InfoGeometry.Topology

namespace Cl11Op

variable {R : Type*} [CommRing R]

instance : Monoid (Cl11Op R) where
  one := one
  mul := mul
  one_mul := by
    intro A
    change Cl11Op.mul Cl11Op.one A = A
    ext <;> simp [Cl11Op.one, Cl11Op.mul]
  mul_one := by
    intro A
    change Cl11Op.mul A Cl11Op.one = A
    ext <;> simp [Cl11Op.one, Cl11Op.mul]
  mul_assoc := by
    intro A B C
    change Cl11Op.mul (Cl11Op.mul A B) C = Cl11Op.mul A (Cl11Op.mul B C)
    ext <;> simp [Cl11Op.mul] <;> ring

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
  simp [matrixBlack, matrixEdge, toMatrix, nodeBlack, edgeTwist,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

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

theorem toMatrix_pathProduct
    {G : ChiralDigraph}
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → Cl11Op R)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    toMatrix (DirectedPath.product edgeWeight p) =
      DirectedPath.product (fun a b h => toMatrix (edgeWeight a b h)) p := by
  induction p with
  | refl => exact toMatrix_one
  | cons h p ih =>
      simp only [DirectedPath.product]
      change toMatrix (Cl11Op.mul _ _) = _
      rw [toMatrix_mul, ih]

end Cl11Op

end InfoGeometry.Holography.PlabicKrein
