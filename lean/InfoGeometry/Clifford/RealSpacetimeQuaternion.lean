/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.HestenesCliffordDimension
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A real quaternion matrix realization of the full spacetime algebra

The carrier is the existing native `CliffordAlgebra Q14`, with signature
`(+---)`. The representation takes values in the full noncommutative algebra
of two by two matrices over real quaternions. Surjectivity is constructed
using quaternion diagonal blocks and matrix units; dimension then gives
injectivity. No scalar imaginary unit or complex coefficient field is used.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealSpacetimeQuaternion

open HestenesCl14
open scoped Matrix

abbrev QuaternionMatrix := Matrix (Fin 2) (Fin 2) (Quaternion ℝ)

def quaternionI : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def quaternionJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def quaternionK : Quaternion ℝ := ⟨0, 0, 0, 1⟩

/-- The time generator is diagonal; each spatial generator is off diagonal. -/
def vectorMatrix : V14 →ₗ[ℝ] QuaternionMatrix where
  toFun v := !![⟨v 0, 0, 0, 0⟩, ⟨0, v 1, v 2, v 3⟩;
               ⟨0, v 1, v 2, v 3⟩, ⟨-v 0, 0, 0, 0⟩]
  map_add' v w := by
    apply Matrix.ext
    intro i j <;> fin_cases i <;> fin_cases j <;> ext <;> simp
  map_smul' r v := by
    apply Matrix.ext
    intro i j <;> fin_cases i <;> fin_cases j <;> ext <;> simp

theorem vectorMatrix_sq (v : V14) :
    vectorMatrix v * vectorMatrix v = algebraMap ℝ QuaternionMatrix (Q14 v) := by
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    simp [vectorMatrix, Q14_apply, qCoeff, Fin.sum_univ_four,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;> ring

/-- The universal property supplies an actual algebra homomorphism. -/
def quaternionRep : Cl14 →ₐ[ℝ] QuaternionMatrix :=
  CliffordAlgebra.lift Q14 ⟨vectorMatrix, vectorMatrix_sq⟩

@[simp] theorem quaternionRep_iota (v : V14) :
    quaternionRep (ι14 v) = vectorMatrix v := by
  exact CliffordAlgebra.lift_ι_apply _ _ v

@[simp] theorem quaternionRep_gamma (i : Fin 4) :
    quaternionRep (gamma i) = vectorMatrix (basisVec i) := by
  exact quaternionRep_iota _

/-- A quaternion embedded diagonally, expressed intrinsically using bivectors. -/
def diagonalQuaternion (q : Quaternion ℝ) : Cl14 :=
  q.re • 1 + q.imI • (gamma 2 * gamma 3) +
    q.imJ • (gamma 3 * gamma 1) + q.imK • (gamma 1 * gamma 2)

@[simp] theorem quaternionRep_diagonalQuaternion (q : Quaternion ℝ) :
    quaternionRep (diagonalQuaternion q) = !![q, 0; 0, q] := by
  simp only [diagonalQuaternion, map_add, map_smul, map_one, map_mul,
    quaternionRep_gamma]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    simp [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The first diagonal matrix unit in the intrinsic Clifford algebra. -/
def timeProjector : Cl14 := (1 / 2 : ℝ) • (1 + gamma 0)

@[simp] theorem quaternionRep_timeProjector :
    quaternionRep timeProjector = !![1, 0; 0, 0] := by
  simp only [timeProjector, map_smul, map_add, map_one, quaternionRep_gamma]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec]

/-- The real off-diagonal swap is a product of three spatial generators. -/
def spatialSwap : Cl14 := -(gamma 1 * gamma 2 * gamma 3)

@[simp] theorem quaternionRep_spatialSwap :
    quaternionRep spatialSwap = !![0, 1; 1, 0] := by
  simp only [spatialSwap, map_neg, map_mul, quaternionRep_gamma]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

/-- An explicit preimage of every quaternion matrix. -/
def matrixPreimage (A : QuaternionMatrix) : Cl14 :=
  timeProjector * diagonalQuaternion (A 0 0) +
    timeProjector * spatialSwap * diagonalQuaternion (A 0 1) +
    (1 - timeProjector) * spatialSwap * diagonalQuaternion (A 1 0) +
    (1 - timeProjector) * diagonalQuaternion (A 1 1)

theorem quaternionRep_matrixPreimage (A : QuaternionMatrix) :
    quaternionRep (matrixPreimage A) = A := by
  simp only [matrixPreimage, map_add, map_mul, map_sub, map_one,
    quaternionRep_timeProjector, quaternionRep_spatialSwap,
    quaternionRep_diagonalQuaternion]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem quaternionRep_surjective : Function.Surjective quaternionRep :=
  fun A => ⟨matrixPreimage A, quaternionRep_matrixPreimage A⟩

theorem quaternionMatrix_finrank : Module.finrank ℝ QuaternionMatrix = 16 := by
  rw [Module.finrank_matrix, Quaternion.finrank_eq_four]
  norm_num

theorem quaternionRep_injective : Function.Injective quaternionRep := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := quaternionRep.toLinearMap) ?_).2 quaternionRep_surjective
  rw [HestenesEvenPauliEquiv.cliffordAlgebra14_finrank, quaternionMatrix_finrank]

/-- The full real algebra equivalence `Cl(1,3) ≃ M₂(ℍ)`. -/
def cl13QuaternionEquiv : Cl14 ≃ₐ[ℝ] QuaternionMatrix :=
  AlgEquiv.ofBijective quaternionRep ⟨quaternionRep_injective, quaternionRep_surjective⟩

/-- The realized carrier is noncommutative on its actual Clifford generators. -/
theorem gamma_one_two_ne : gamma 1 * gamma 2 ≠ gamma 2 * gamma 1 := by
  intro h
  have he := congrArg (fun a => (quaternionRep a 0 0).imK) h
  norm_num [map_mul, vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two] at he

/-- Closed noncommutation witnesses in the full quaternion matrix algebra. -/
theorem quaternionMatrix_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) (Quaternion ℝ), A * B ≠ B * A := by
  refine ⟨vectorMatrix (basisVec 1), vectorMatrix (basisVec 2), ?_⟩
  intro h
  apply gamma_one_two_ne
  apply quaternionRep_injective
  simpa only [map_mul, quaternionRep_gamma] using h

end InfoGeometry.Clifford.RealSpacetimeQuaternion
