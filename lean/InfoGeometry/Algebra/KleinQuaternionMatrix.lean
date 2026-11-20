/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.KleinCentralQuaternion
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Matrix splitting of the central Klein quaternion model

For units `u,t`, the native quaternion algebra with parameters
`(-1,u+u⁻¹,t)` maps to the full two-by-two matrix algebra. Over a field,
the map is an algebra equivalence when `u-u⁻¹ ≠ 0`, with an explicit
inverse. At `u=u⁻¹` the rank-four quaternion carrier has a nonzero
square-zero kernel element, so the displayed matrix map is not faithful.

This is a parameter specialization and splitting theorem. It does not
assert a global splitting over a universal symbolic center. Quaternion
conjugation is not identified with the matrix C*-adjoint.
-/

namespace InfoGeometry.Algebra.KleinQuaternionMatrix

open Matrix

section CommutativeRing

variable {R : Type*} [CommRing R]

/-- The full matrix carrier is noncommutative whenever its coefficient ring is nontrivial. -/
theorem exists_noncommuting_matrices [Nontrivial R] :
    ∃ a b : Matrix (Fin 2) (Fin 2) R, a * b ≠ b * a := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have he : (1 : R) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  exact one_ne_zero he

/-- The two transverse eigenvalues are inverse units. -/
def transverseMatrix (u : Rˣ) : Matrix (Fin 2) (Fin 2) R :=
  !![(u : R), 0; 0, (↑(u⁻¹) : R)]

/-- The glide has the prescribed scalar square. -/
def glideMatrix (t : Rˣ) : Matrix (Fin 2) (Fin 2) R :=
  !![0, (t : R); 1, 0]

/-- Distinct transverse eigenvalues give an explicit noncommutativity witness. -/
theorem transverse_glide_noncommute (u t : Rˣ)
    (hδ : (u : R) - (↑(u⁻¹) : R) ≠ 0) :
    transverseMatrix u * glideMatrix t ≠ glideMatrix t * transverseMatrix u := by
  intro h
  have he : (↑(u⁻¹) : R) = (u : R) := by
    simpa [transverseMatrix, glideMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) h
  exact hδ (sub_eq_zero.mpr he.symm)

/-- The actual matrices satisfy Mathlib's quaternion-basis relations. -/
def matrixBasis (u t : Rˣ) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R)
      (-1 : R) ((u : R) + (↑(u⁻¹) : R)) (t : R) where
  i := transverseMatrix u
  j := glideMatrix t
  k := transverseMatrix u * glideMatrix t
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_mul]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glideMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := rfl
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseMatrix, glideMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- The representation uses the native quaternion universal map. -/
def toMatrix (u t : Rˣ) :
    QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R) →ₐ[R]
      Matrix (Fin 2) (Fin 2) R :=
  (matrixBasis u t).liftHom

theorem toMatrix_apply (u t : Rˣ)
    (q : QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R)) :
    toMatrix u t q =
      !![q.re + q.imI * (u : R), (t : R) * (q.imJ + q.imK * (u : R));
        q.imJ + q.imK * (↑(u⁻¹) : R), q.re + q.imI * (↑(u⁻¹) : R)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, QuaternionAlgebra.Basis.liftHom_apply,
      QuaternionAlgebra.Basis.lift, matrixBasis, transverseMatrix,
      glideMatrix, Algebra.algebraMap_eq_smul_one]
  ring

theorem trace_toMatrix (u t : Rˣ)
    (q : QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R)) :
    Matrix.trace (toMatrix u t q) = KleinCentralQuaternion.reducedTrace q := by
  rw [toMatrix_apply, Matrix.trace_fin_two_of]
  dsimp [KleinCentralQuaternion.reducedTrace]
  ring

theorem det_toMatrix (u t : Rˣ)
    (q : QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R)) :
    Matrix.det (toMatrix u t q) = KleinCentralQuaternion.reducedNorm q := by
  rw [toMatrix_apply, Matrix.det_fin_two_of]
  calc
    (q.re + q.imI * (u : R)) * (q.re + q.imI * (↑(u⁻¹) : R)) -
        ((t : R) * (q.imJ + q.imK * (u : R))) *
          (q.imJ + q.imK * (↑(u⁻¹) : R)) =
      q.re ^ 2 + ((u : R) + (↑(u⁻¹) : R)) * q.re * q.imI +
        q.imI ^ 2 * ((u : R) * (↑(u⁻¹) : R)) -
        (t : R) * (q.imJ ^ 2 + ((u : R) + (↑(u⁻¹) : R)) * q.imJ * q.imK +
          q.imK ^ 2 * ((u : R) * (↑(u⁻¹) : R))) := by ring
    _ = KleinCentralQuaternion.reducedNorm q := by
      simp only [Units.mul_inv, mul_one, KleinCentralQuaternion.reducedNorm]

/-- The repeated-root specialization retains a nonzero quaternion direction. -/
def branchKernel (u t : Rˣ) :
    QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R) :=
  ⟨-(u : R), 1, 0, 0⟩

theorem branchKernel_ne_zero [Nontrivial R] (u t : Rˣ) : branchKernel u t ≠ 0 := by
  intro h
  have hi : (1 : R) = 0 := by
    simpa [branchKernel] using congrArg QuaternionAlgebra.imI h
  exact one_ne_zero hi

theorem branchKernel_square (u t : Rˣ) (h : (u : R) = (↑(u⁻¹) : R)) :
    branchKernel u t * branchKernel u t = 0 := by
  have hu : (u : R) * (u : R) = 1 := by
    simpa only [← h] using Units.mul_inv u
  ext <;> simp [branchKernel, ← h, hu]

theorem branchKernel_image (u t : Rˣ) (h : (u : R) = (↑(u⁻¹) : R)) :
    toMatrix u t (branchKernel u t) = 0 := by
  rw [toMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [branchKernel, ← h]

theorem toMatrix_not_injective_of_branch [Nontrivial R] (u t : Rˣ)
    (h : (u : R) = (↑(u⁻¹) : R)) : ¬ Function.Injective (toMatrix u t) := by
  intro hinj
  apply branchKernel_ne_zero u t
  apply hinj
  rw [branchKernel_image u t h, map_zero]

end CommutativeRing

section Field

variable {R : Type*} [Field R]

/-- Solve for the four quaternion coefficients when the two eigenvalues differ. -/
def ofMatrix (u t : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R) where
  re := ((u : R) * M 1 1 - (↑(u⁻¹) : R) * M 0 0) /
    ((u : R) - (↑(u⁻¹) : R))
  imI := (M 0 0 - M 1 1) / ((u : R) - (↑(u⁻¹) : R))
  imJ := ((u : R) * M 1 0 - (↑(u⁻¹) : R) * (↑(t⁻¹) : R) * M 0 1) /
    ((u : R) - (↑(u⁻¹) : R))
  imK := ((↑(t⁻¹) : R) * M 0 1 - M 1 0) /
    ((u : R) - (↑(u⁻¹) : R))

theorem ofMatrix_toMatrix (u t : Rˣ)
    (hδ : (u : R) - (↑(u⁻¹) : R) ≠ 0)
    (q : QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R)) :
    ofMatrix u t (toMatrix u t q) = q := by
  have ht (x : R) : (↑(t⁻¹) : R) * ((t : R) * x) = x := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [toMatrix_apply]
  apply QuaternionAlgebra.ext
  · change ((u : R) * (q.re + q.imI * (↑(u⁻¹) : R)) -
        (↑(u⁻¹) : R) * (q.re + q.imI * (u : R))) /
        ((u : R) - (↑(u⁻¹) : R)) = q.re
    rw [div_eq_iff hδ]
    ring
  · change ((q.re + q.imI * (u : R)) - (q.re + q.imI * (↑(u⁻¹) : R))) /
        ((u : R) - (↑(u⁻¹) : R)) = q.imI
    rw [div_eq_iff hδ]
    ring
  · change ((u : R) * (q.imJ + q.imK * (↑(u⁻¹) : R)) -
        (↑(u⁻¹) : R) * (↑(t⁻¹) : R) * ((t : R) * (q.imJ + q.imK * (u : R)))) /
        ((u : R) - (↑(u⁻¹) : R)) = q.imJ
    rw [div_eq_iff hδ]
    simp only [mul_assoc, ht]
    ring
  · change ((↑(t⁻¹) : R) * ((t : R) * (q.imJ + q.imK * (u : R))) -
        (q.imJ + q.imK * (↑(u⁻¹) : R))) /
        ((u : R) - (↑(u⁻¹) : R)) = q.imK
    rw [div_eq_iff hδ, ht]
    ring

theorem toMatrix_ofMatrix (u t : Rˣ)
    (hδ : (u : R) - (↑(u⁻¹) : R) ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) R) : toMatrix u t (ofMatrix u t M) = M := by
  rw [toMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · change ((u : R) * M 1 1 - (↑(u⁻¹) : R) * M 0 0) /
        ((u : R) - (↑(u⁻¹) : R)) +
        ((M 0 0 - M 1 1) / ((u : R) - (↑(u⁻¹) : R))) * (u : R) = M 0 0
    rw [div_mul_eq_mul_div₀, ← add_div, div_eq_iff hδ]
    ring
  · change (t : R) *
        (((u : R) * M 1 0 - (↑(u⁻¹) : R) * (↑(t⁻¹) : R) * M 0 1) /
            ((u : R) - (↑(u⁻¹) : R)) +
          (((↑(t⁻¹) : R) * M 0 1 - M 1 0) /
            ((u : R) - (↑(u⁻¹) : R))) * (u : R)) = M 0 1
    rw [div_mul_eq_mul_div₀, ← add_div, ← mul_div_assoc, div_eq_iff hδ]
    calc
      (t : R) * (((u : R) * M 1 0 - (↑(u⁻¹) : R) * (↑(t⁻¹) : R) * M 0 1) +
          ((↑(t⁻¹) : R) * M 0 1 - M 1 0) * (u : R)) =
        ((t : R) * (↑(t⁻¹) : R)) * M 0 1 * ((u : R) - (↑(u⁻¹) : R)) := by ring
      _ = M 0 1 * ((u : R) - (↑(u⁻¹) : R)) := by rw [Units.mul_inv, one_mul]
  · change ((u : R) * M 1 0 - (↑(u⁻¹) : R) * (↑(t⁻¹) : R) * M 0 1) /
        ((u : R) - (↑(u⁻¹) : R)) +
        (((↑(t⁻¹) : R) * M 0 1 - M 1 0) /
          ((u : R) - (↑(u⁻¹) : R))) * (↑(u⁻¹) : R) = M 1 0
    rw [div_mul_eq_mul_div₀, ← add_div, div_eq_iff hδ]
    ring
  · change ((u : R) * M 1 1 - (↑(u⁻¹) : R) * M 0 0) /
        ((u : R) - (↑(u⁻¹) : R)) +
        ((M 0 0 - M 1 1) / ((u : R) - (↑(u⁻¹) : R))) * (↑(u⁻¹) : R) = M 1 1
    rw [div_mul_eq_mul_div₀, ← add_div, div_eq_iff hδ]
    ring

/-- An actual algebra equivalence to all matrices away from the repeated-root locus. -/
noncomputable def matrixEquiv (u t : Rˣ)
    (hδ : (u : R) - (↑(u⁻¹) : R) ≠ 0) :
    QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R) ≃ₐ[R]
      Matrix (Fin 2) (Fin 2) R := by
  refine AlgEquiv.ofBijective (toMatrix u t) ?_
  have hL : Function.LeftInverse (ofMatrix u t) (toMatrix u t) :=
    ofMatrix_toMatrix u t hδ
  have hR : Function.RightInverse (ofMatrix u t) (toMatrix u t) :=
    toMatrix_ofMatrix u t hδ
  exact ⟨hL.injective, hR.surjective⟩

@[simp] theorem matrixEquiv_apply (u t : Rˣ)
    (hδ : (u : R) - (↑(u⁻¹) : R) ≠ 0)
    (q : QuaternionAlgebra R (-1) ((u : R) + (↑(u⁻¹) : R)) (t : R)) :
    matrixEquiv u t hδ q = toMatrix u t q := rfl

theorem matrixEquiv_symm_apply (u t : Rˣ)
    (hδ : (u : R) - (↑(u⁻¹) : R) ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) R) :
    (matrixEquiv u t hδ).symm M = ofMatrix u t M := by
  apply (matrixEquiv u t hδ).injective
  rw [AlgEquiv.apply_symm_apply, matrixEquiv_apply, toMatrix_ofMatrix u t hδ]

end Field

end InfoGeometry.Algebra.KleinQuaternionMatrix
