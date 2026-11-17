/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.RealSpacetimeQuaternion
import InfoGeometry.Canonical.HestenesHermitianAdjoint

/-!
# Real coordinates and reversion for all even spacetime spinors

The coordinates below are a proved linear equivalence on the complete native
even Clifford algebra. They retain the noncommutative multiplication through
the faithful quaternion matrix representation. The scalar readout is the
normalized real quaternion trace, and its normalization is explicit.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealSpacetimeSpinor

open HestenesCl14 HestenesKreinMatrixBridge HestenesHermitianAdjoint
open RealSpacetimeQuaternion
open scoped Matrix

def timeMatrix : QuaternionMatrix := !![1, 0; 0, -1]

@[simp] theorem quaternionRep_gamma_zero : quaternionRep (gamma 0) = timeMatrix := by
  rw [quaternionRep_gamma]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    simp [vectorMatrix, basisVec, timeMatrix]

@[simp] theorem timeMatrix_sq : timeMatrix * timeMatrix = 1 := by
  rw [← quaternionRep_gamma_zero, ← map_mul, gamma_zero_sq, map_one]

/-- The representation of Clifford reversion on quaternion matrices. -/
def matrixReverse (A : QuaternionMatrix) : QuaternionMatrix :=
  timeMatrix * star A * timeMatrix

theorem matrixReverse_mul (A B : QuaternionMatrix) :
    matrixReverse (A * B) = matrixReverse B * matrixReverse A := by
  simp only [matrixReverse, star_mul]
  calc
    timeMatrix * (star B * star A) * timeMatrix =
        timeMatrix * star B * (timeMatrix * timeMatrix) * star A * timeMatrix := by
      rw [timeMatrix_sq]
      simp only [mul_one, mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem quaternionRep_reverse (a : Cl14) :
    quaternionRep (CliffordAlgebra.reverse a) = matrixReverse (quaternionRep a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      simp only [CliffordAlgebra.reverse.commutes, quaternionRep.commutes]
      apply Matrix.ext
      intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
        simp [matrixReverse, timeMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.star_apply, Algebra.algebraMap_eq_smul_one]
  | ι v =>
      simp only [CliffordAlgebra.reverse_ι, quaternionRep_iota]
      apply Matrix.ext
      intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
        simp [matrixReverse, timeMatrix, vectorMatrix, Matrix.mul_apply,
          Fin.sum_univ_two, Matrix.star_apply]
  | mul a b ha hb =>
      simp only [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb, matrixReverse_mul]
  | add a b ha hb =>
      simp only [map_add, ha, hb, matrixReverse, star_add, mul_add, add_mul]

theorem quaternionRep_hestenesAdjoint (x : ClPlus14) :
    quaternionRep (hestenesAdjoint x : Cl14) = star (quaternionRep (x : Cl14)) := by
  rw [hestenesAdjoint_val, map_mul, map_mul, quaternionRep_gamma_zero,
    quaternionRep_reverse, matrixReverse]
  calc
    timeMatrix * (timeMatrix * star (quaternionRep (x : Cl14)) * timeMatrix) * timeMatrix =
        (timeMatrix * timeMatrix) * star (quaternionRep (x : Cl14)) *
          (timeMatrix * timeMatrix) := by simp only [mul_assoc]
    _ = _ := by rw [timeMatrix_sq]; simp

/-- The complete even matrix shape; both quaternion slots are arbitrary. -/
def evenMatrix (p q : Quaternion ℝ) : QuaternionMatrix := !![p, q; -q, p]

theorem evenMatrix_mul (p q r s : Quaternion ℝ) :
    evenMatrix p q * evenMatrix r s = evenMatrix (p * r - q * s) (p * s + q * r) := by
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

private theorem even_shape_add {A B : QuaternionMatrix}
    (hA : A = evenMatrix (A 0 0) (A 0 1))
    (hB : B = evenMatrix (B 0 0) (B 0 1)) :
    A + B = evenMatrix ((A + B) 0 0) ((A + B) 0 1) := by
  rw [hA, hB]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> simp [evenMatrix]

private theorem even_shape_mul {A B : QuaternionMatrix}
    (hA : A = evenMatrix (A 0 0) (A 0 1))
    (hB : B = evenMatrix (B 0 0) (B 0 1)) :
    A * B = evenMatrix ((A * B) 0 0) ((A * B) 0 1) := by
  rw [hA, hB, evenMatrix_mul]
  rfl

private theorem vector_pair_even_shape (v w : V14) :
    vectorMatrix v * vectorMatrix w =
      evenMatrix ((vectorMatrix v * vectorMatrix w) 0 0)
        ((vectorMatrix v * vectorMatrix w) 0 1) := by
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    simp [vectorMatrix, evenMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem quaternionRep_even_shape (x : ClPlus14) :
    quaternionRep (x : Cl14) =
      evenMatrix (quaternionRep (x : Cl14) 0 0) (quaternionRep (x : Cl14) 0 1) := by
  rcases x with ⟨x, hx⟩
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [quaternionRep.commutes]
      apply Matrix.ext
      intro i j <;> fin_cases i <;> fin_cases j <;>
        simp [evenMatrix, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using even_shape_add ihx ihy
  | ι_mul_ι_mul v w x hx ihx =>
      simpa only [map_mul, quaternionRep_iota] using
        even_shape_mul (vector_pair_even_shape v w) ihx

def spinorCoordinates : ClPlus14 →ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ) where
  toFun x := (quaternionRep (x : Cl14) 0 0, quaternionRep (x : Cl14) 0 1)
  map_add' x y := by simp [map_add]; rfl
  map_smul' r x := by simp [map_smul]; rfl

def evenPair (i j : Fin 4) : ClPlus14 :=
  (CliffordAlgebra.even.ι Q14).bilin (basisVec i) (basisVec j)

@[simp] theorem evenPair_val (i j : Fin 4) :
    (evenPair i j : Cl14) = gamma i * gamma j := rfl

def evenQuaternion (q : Quaternion ℝ) : ClPlus14 :=
  q.re • 1 + q.imI • evenPair 2 3 +
    q.imJ • evenPair 3 1 + q.imK • evenPair 1 2

@[simp] theorem evenQuaternion_val (q : Quaternion ℝ) :
    (evenQuaternion q : Cl14) = diagonalQuaternion q := rfl

/-- Oriented spacetime volume `γ₀γ₁γ₂γ₃` in the even subalgebra. -/
def volume : ClPlus14 := evenPair 0 1 * evenPair 2 3

@[simp] theorem quaternionRep_volume :
    quaternionRep (volume : Cl14) = !![0, -1; 1, 0] := by
  simp only [volume, Subalgebra.coe_mul, evenPair_val, map_mul, quaternionRep_gamma]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

def spinorOfCoordinates (x : Quaternion ℝ × Quaternion ℝ) : ClPlus14 :=
  evenQuaternion x.1 - volume * evenQuaternion x.2

theorem quaternionRep_spinorOfCoordinates (x : Quaternion ℝ × Quaternion ℝ) :
    quaternionRep (spinorOfCoordinates x : Cl14) = evenMatrix x.1 x.2 := by
  simp only [spinorOfCoordinates, Subalgebra.coe_sub, Subalgebra.coe_mul,
    evenQuaternion_val, map_sub, map_mul, quaternionRep_volume,
    quaternionRep_diagonalQuaternion]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem spinorCoordinates_injective : Function.Injective spinorCoordinates := by
  intro x y h
  apply Subtype.ext
  apply quaternionRep_injective
  rw [quaternionRep_even_shape x, quaternionRep_even_shape y]
  exact congrArg₂ evenMatrix (congrArg Prod.fst h) (congrArg Prod.snd h)

@[simp] theorem spinorCoordinates_spinorOfCoordinates (x : Quaternion ℝ × Quaternion ℝ) :
    spinorCoordinates (spinorOfCoordinates x) = x := by
  simp only [spinorCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
    quaternionRep_spinorOfCoordinates, evenMatrix]
  exact Prod.eta x

/-- Every native even spinor has exactly two real quaternion coordinates. -/
def spinorCoordinateEquiv : ClPlus14 ≃ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ) :=
  LinearEquiv.ofBijective spinorCoordinates
    ⟨spinorCoordinates_injective,
      fun x => ⟨spinorOfCoordinates x, spinorCoordinates_spinorOfCoordinates x⟩⟩

theorem spinorCoordinates_mul (x y : ClPlus14) :
    spinorCoordinates (x * y) =
      ((spinorCoordinates x).1 * (spinorCoordinates y).1 -
        (spinorCoordinates x).2 * (spinorCoordinates y).2,
       (spinorCoordinates x).1 * (spinorCoordinates y).2 +
        (spinorCoordinates x).2 * (spinorCoordinates y).1) := by
  change (quaternionRep ((x : Cl14) * (y : Cl14)) 0 0,
      quaternionRep ((x : Cl14) * (y : Cl14)) 0 1) = _
  rw [map_mul, quaternionRep_even_shape x, quaternionRep_even_shape y, evenMatrix_mul]
  rfl

theorem spinorCoordinates_reverseEven (x : ClPlus14) :
    spinorCoordinates (reverseEven x) =
      (star (spinorCoordinates x).1, star (spinorCoordinates x).2) := by
  change (quaternionRep (CliffordAlgebra.reverse (x : Cl14)) 0 0,
    quaternionRep (CliffordAlgebra.reverse (x : Cl14)) 0 1) = _
  rw [quaternionRep_reverse, quaternionRep_even_shape x]
  simp [spinorCoordinates, matrixReverse, timeMatrix, evenMatrix,
    Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem spinorCoordinates_hestenesAdjoint (x : ClPlus14) :
    spinorCoordinates (hestenesAdjoint x) =
      (star (spinorCoordinates x).1, -star (spinorCoordinates x).2) := by
  change (quaternionRep (hestenesAdjoint x : Cl14) 0 0,
    quaternionRep (hestenesAdjoint x : Cl14) 0 1) = _
  rw [quaternionRep_hestenesAdjoint, quaternionRep_even_shape x]
  simp [spinorCoordinates, evenMatrix, Matrix.star_apply]

/-- The real scalar coefficient, normalized so that `scalar 1 = 1`. -/
def scalar : Cl14 →ₗ[ℝ] ℝ where
  toFun a := ((quaternionRep a 0 0).re + (quaternionRep a 1 1).re) / 2
  map_add' a b := by simp [map_add]; ring
  map_smul' r a := by simp [map_smul]; ring

@[simp] theorem scalar_one : scalar 1 = 1 := by simp [scalar]

theorem scalar_even (x : ClPlus14) :
    scalar (x : Cl14) = (spinorCoordinates x).1.re := by
  change ((quaternionRep (x : Cl14) 0 0).re +
    (quaternionRep (x : Cl14) 1 1).re) / 2 = _
  rw [quaternionRep_even_shape x]
  simp [evenMatrix, spinorCoordinates]

theorem scalar_mul_comm (a b : Cl14) : scalar (a * b) = scalar (b * a) := by
  simp only [scalar, LinearMap.coe_mk, AddHom.coe_mk, map_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end InfoGeometry.Clifford.RealSpacetimeSpinor
