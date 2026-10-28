/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CliffordDirac.Defect
import InfoGeometry.OperatorAlgebra.CliffordDirac.Grading
import InfoGeometry.UnifiedMatrixBasis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Clifford operators with arbitrary matrix coefficients

The spin and multiplicity actions live in the full complex matrix algebra.
Their cross commutation does not impose commutation on either factor.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordDirac

open Matrix
open scoped Kronecker
open UnifiedMatrixBasis (σ₁ σ₂)

abbrev SpinMatrix (n : Type*) := Matrix (Fin 2 × n) (Fin 2 × n) ℂ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spin-factor action. -/
def spinLift (S : Matrix (Fin 2) (Fin 2) ℂ) : SpinMatrix n :=
  S ⊗ₖ (1 : Matrix n n ℂ)

/-- The multiplicity-factor action. -/
def coefficientLift (A : Matrix n n ℂ) : SpinMatrix n :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A

omit [Fintype n] in
@[simp] theorem spinLift_zero : spinLift (n := n) 0 = 0 := Matrix.zero_kronecker _
omit [Fintype n] in
@[simp] theorem spinLift_one : spinLift (n := n) 1 = 1 := Matrix.one_kronecker_one
omit [Fintype n] [DecidableEq n] in
@[simp] theorem coefficientLift_zero : coefficientLift (n := n) 0 = 0 :=
  Matrix.kronecker_zero _

omit [Fintype n] in
theorem spinLift_add (S T : Matrix (Fin 2) (Fin 2) ℂ) :
    spinLift (n := n) (S + T) = spinLift S + spinLift T := Matrix.add_kronecker _ _ _

theorem spinLift_mul (S T : Matrix (Fin 2) (Fin 2) ℂ) :
    spinLift (n := n) (S * T) = spinLift S * spinLift T := by
  simpa only [spinLift, one_mul] using
    Matrix.mul_kronecker_mul S T (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)

omit [Fintype n] [DecidableEq n] in
theorem coefficientLift_add (A B : Matrix n n ℂ) :
    coefficientLift (A + B) = coefficientLift A + coefficientLift B :=
  Matrix.kronecker_add _ _ _

omit [Fintype n] [DecidableEq n] in
theorem coefficientLift_sub (A B : Matrix n n ℂ) :
    coefficientLift (A - B) = coefficientLift A - coefficientLift B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [coefficientLift, Matrix.kroneckerMap_apply, mul_sub]

omit [DecidableEq n] in
theorem coefficientLift_mul (A B : Matrix n n ℂ) :
    coefficientLift (A * B) = coefficientLift A * coefficientLift B := by
  simpa only [coefficientLift, one_mul] using
    Matrix.mul_kronecker_mul (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) A B

theorem spinLift_commute (S : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix n n ℂ) :
    Commute (spinLift S) (coefficientLift A) := by
  change (S ⊗ₖ 1) * (1 ⊗ₖ A) = (1 ⊗ₖ A) * (S ⊗ₖ 1)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

omit [Fintype n] [DecidableEq n] in
theorem coefficientLift_injective : Function.Injective (coefficientLift (n := n)) := by
  intro A B h
  ext i j
  have hij := congrArg (fun M : SpinMatrix n => M (0, i) (0, j)) h
  simpa [coefficientLift, Matrix.kroneckerMap_apply, Matrix.one_apply] using hij

omit [Fintype n] [DecidableEq n] in
@[simp] theorem coefficientLift_eq_zero_iff (A : Matrix n n ℂ) :
    coefficientLift A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply coefficientLift_injective
    simpa only [coefficientLift_zero] using h
  · rintro rfl
    exact coefficientLift_zero

omit [DecidableEq n] in
theorem coefficientLift_lie (A B : Matrix n n ℂ) :
    ⁅coefficientLift A, coefficientLift B⁆ = coefficientLift ⁅A, B⁆ := by
  simp only [Ring.lie_def, coefficientLift_sub, coefficientLift_mul]

omit [DecidableEq n] in
theorem coefficientLift_lie_ne_zero_iff (A B : Matrix n n ℂ) :
    ⁅coefficientLift A, coefficientLift B⁆ ≠ 0 ↔ ⁅A, B⁆ ≠ 0 := by
  rw [coefficientLift_lie]
  exact not_congr (coefficientLift_eq_zero_iff _)

theorem coefficient_spin_lie (S : Matrix (Fin 2) (Fin 2) ℂ)
    (A B : Matrix n n ℂ) :
    ⁅coefficientLift A, spinLift S * coefficientLift B⁆ =
      spinLift S * coefficientLift ⁅A, B⁆ := by
  rw [← coefficientLift_lie]
  simp only [Ring.lie_def]
  rw [← mul_assoc (coefficientLift A) (spinLift S) (coefficientLift B),
    (spinLift_commute S A).symm.eq]
  noncomm_ring

omit [Fintype n] in
theorem spinLift_isHermitian {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : S.IsHermitian) :
    (spinLift (n := n) S).IsHermitian := by
  change (S ⊗ₖ (1 : Matrix n n ℂ))ᴴ = S ⊗ₖ (1 : Matrix n n ℂ)
  rw [Matrix.conjTranspose_kronecker, hS.eq, Matrix.conjTranspose_one]

omit [Fintype n] [DecidableEq n] in
theorem coefficientLift_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (coefficientLift A).IsHermitian := by
  change ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A)ᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

def spinX : SpinMatrix n := spinLift σ₁
def spinY : SpinMatrix n := spinLift σ₂

private theorem pauliIdentity_eq_one : UnifiedMatrixBasis.I₂ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnifiedMatrixBasis.I₂]

theorem spinX_sq : spinX (n := n) * spinX = 1 := by
  change spinLift (n := n) σ₁ * spinLift σ₁ = 1
  rw [← spinLift_mul, UnifiedMatrixBasis.pauli_square.1,
    pauliIdentity_eq_one, spinLift_one]

theorem spinY_sq : spinY (n := n) * spinY = 1 := by
  change spinLift (n := n) σ₂ * spinLift σ₂ = 1
  rw [← spinLift_mul, UnifiedMatrixBasis.pauli_square.2.1,
    pauliIdentity_eq_one, spinLift_one]

theorem spin_anticommute : spinX (n := n) * spinY + spinY * spinX = 0 := by
  simp only [spinX, spinY, ← spinLift_mul, ← spinLift_add,
    UnifiedMatrixBasis.pauli_anticomm.1, spinLift_zero]

theorem spinX_commute (A : Matrix n n ℂ) : Commute spinX (coefficientLift A) :=
  spinLift_commute _ _

theorem spinY_commute (A : Matrix n n ℂ) : Commute spinY (coefficientLift A) :=
  spinLift_commute _ _

omit [Fintype n] in
theorem spinX_isHermitian : (spinX (n := n)).IsHermitian := by
  apply spinLift_isHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₁, Matrix.conjTranspose_apply]

omit [Fintype n] in
theorem spinY_isHermitian : (spinY (n := n)).IsHermitian := by
  apply spinLift_isHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₂, Matrix.conjTranspose_apply]

omit [Fintype n] in
theorem spinX_not_isDiag [Nonempty n] : ¬ (spinX (n := n)).IsDiag := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty n›
  have hz : spinX (0, i) (1, i) = 0 := h (by simp)
  simp [spinX, spinLift, σ₁, Matrix.kroneckerMap_apply] at hz

omit [Fintype n] in
theorem spinY_not_isDiag [Nonempty n] : ¬ (spinY (n := n)).IsDiag := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty n›
  have hz : spinY (0, i) (1, i) = 0 := h (by simp)
  simp [spinY, spinLift, σ₂, Matrix.kroneckerMap_apply] at hz

def matrixDirac (A B : Matrix n n ℂ) : SpinMatrix n :=
  spinX * coefficientLift A + spinY * coefficientLift B

def matrixSecondCharge (A B : Matrix n n ℂ) : SpinMatrix n :=
  spinY * coefficientLift A - spinX * coefficientLift B

def matrixLaplacian (A B : Matrix n n ℂ) : SpinMatrix n :=
  coefficientLift A * coefficientLift A + coefficientLift B * coefficientLift B

def matrixCurvature (A B : Matrix n n ℂ) : SpinMatrix n :=
  (spinX * spinY) * ⁅coefficientLift A, coefficientLift B⁆

theorem matrixDirac_sq (A B : Matrix n n ℂ) :
    matrixDirac A B * matrixDirac A B = matrixLaplacian A B + matrixCurvature A B := by
  exact clifford_sum_sq _ _ _ _ spinX_sq spinY_sq spin_anticommute
    (spinX_commute A) (spinX_commute B) (spinY_commute A) (spinY_commute B)

theorem matrixDirac_isHermitian {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (matrixDirac A B).IsHermitian := by
  change (spinX * coefficientLift A + spinY * coefficientLift B)ᴴ =
    spinX * coefficientLift A + spinY * coefficientLift B
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    spinX_isHermitian.eq, spinY_isHermitian.eq,
    (coefficientLift_isHermitian hA).eq, (coefficientLift_isHermitian hB).eq]
  rw [(spinX_commute A).symm.eq, (spinY_commute B).symm.eq]

theorem matrixSecondCharge_sq (A B : Matrix n n ℂ) :
    matrixSecondCharge A B * matrixSecondCharge A B =
      matrixDirac A B * matrixDirac A B := by
  exact rotated_clifford_sum_sq spinX_sq spinY_sq spin_anticommute
    (spinX_commute A) (spinX_commute B) (spinY_commute A) (spinY_commute B)

theorem matrixCharges_anticommute (A B : Matrix n n ℂ) :
    matrixDirac A B * matrixSecondCharge A B +
      matrixSecondCharge A B * matrixDirac A B = 0 := by
  exact rotated_clifford_sum_anticommute spinX_sq spinY_sq spin_anticommute
    (spinX_commute A) (spinX_commute B) (spinY_commute A) (spinY_commute B)

theorem matrixSecondCharge_isHermitian {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (matrixSecondCharge A B).IsHermitian := by
  change (spinY * coefficientLift A - spinX * coefficientLift B)ᴴ =
    spinY * coefficientLift A - spinX * coefficientLift B
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    spinX_isHermitian.eq, spinY_isHermitian.eq,
    (coefficientLift_isHermitian hA).eq, (coefficientLift_isHermitian hB).eq]
  rw [(spinY_commute A).symm.eq, (spinX_commute B).symm.eq]

theorem matrixCurvature_ne_zero_iff (A B : Matrix n n ℂ) :
    matrixCurvature A B ≠ 0 ↔ ⁅A, B⁆ ≠ 0 := by
  exact (bivector_mul_ne_zero_iff (g := spinX) (h := spinY)
    spinX_sq spinY_sq spin_anticommute _).trans (coefficientLift_lie_ne_zero_iff A B)

omit [DecidableEq n] in
theorem matrixLaplacian_eq (A B : Matrix n n ℂ) :
    matrixLaplacian A B = coefficientLift (A * A + B * B) := by
  simp only [matrixLaplacian, coefficientLift_add, coefficientLift_mul]

theorem matrixLaplacian_curvature_lie (A B : Matrix n n ℂ) :
    ⁅matrixLaplacian A B, matrixCurvature A B⁆ =
      (spinX * spinY) * coefficientLift ⁅A * A + B * B, ⁅A, B⁆⁆ := by
  simp only [matrixLaplacian_eq, matrixCurvature, coefficientLift_lie,
    spinX, spinY, ← spinLift_mul]
  exact coefficient_spin_lie _ _ _

/-- A self-adjoint nondiagonal coefficient operator. -/
def witnessA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 0]

/-- A second self-adjoint nondiagonal coefficient operator. -/
def witnessB : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 1]

theorem witnessA_isHermitian : witnessA.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessA, Matrix.conjTranspose_apply]

theorem witnessB_isHermitian : witnessB.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessB, Matrix.conjTranspose_apply]

theorem witnessA_not_isDiag : ¬ witnessA.IsDiag := by
  intro h
  have hz : witnessA 0 1 = 0 := h (by decide)
  norm_num [witnessA] at hz

theorem witnessB_not_isDiag : ¬ witnessB.IsDiag := by
  intro h
  have hz : witnessB 0 1 = 0 := h (by decide)
  norm_num [witnessB] at hz

theorem witness_lie : ⁅witnessA, witnessB⁆ = !![0, 2; -2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ring.lie_def, witnessA, witnessB, Matrix.mul_apply, Fin.sum_univ_two]

theorem witness_lie_ne_zero : ⁅witnessA, witnessB⁆ ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [witness_lie] at h01

theorem witness_nested_lie_ne_zero :
    ⁅witnessA * witnessA + witnessB * witnessB, ⁅witnessA, witnessB⁆⁆ ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [Ring.lie_def, witnessA, witnessB, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem witness_curvature_ne_zero : matrixCurvature witnessA witnessB ≠ 0 :=
  (matrixCurvature_ne_zero_iff _ _).2 witness_lie_ne_zero

/-- The two summands of the square fail to commute in the full `4 × 4` algebra. -/
theorem witness_laplacian_curvature_lie_ne_zero :
    ⁅matrixLaplacian witnessA witnessB, matrixCurvature witnessA witnessB⁆ ≠ 0 := by
  rw [matrixLaplacian_curvature_lie]
  apply (bivector_mul_ne_zero_iff (g := spinX) (h := spinY)
    spinX_sq spinY_sq spin_anticommute _).2
  exact (not_congr (coefficientLift_eq_zero_iff _)).2 witness_nested_lie_ne_zero

/-- The square Hamiltonian does not preserve its sum-of-squares summand separately. -/
theorem witness_hamiltonian_laplacian_not_commute :
    ¬ Commute (matrixDirac witnessA witnessB * matrixDirac witnessA witnessB)
      (matrixLaplacian witnessA witnessB) := by
  intro hc
  apply witness_laplacian_curvature_lie_ne_zero
  calc
    _ = ⁅matrixLaplacian witnessA witnessB,
        matrixDirac witnessA witnessB * matrixDirac witnessA witnessB⁆ := by
      rw [matrixDirac_sq]
      simp only [Ring.lie_def]
      noncomm_ring
    _ = 0 := hc.symm.lie_eq

/-- The same Hamiltonian does not preserve the curvature summand separately. -/
theorem witness_hamiltonian_curvature_not_commute :
    ¬ Commute (matrixDirac witnessA witnessB * matrixDirac witnessA witnessB)
      (matrixCurvature witnessA witnessB) := by
  intro hc
  apply witness_laplacian_curvature_lie_ne_zero
  calc
    _ = ⁅matrixDirac witnessA witnessB * matrixDirac witnessA witnessB,
        matrixCurvature witnessA witnessB⁆ := by
      rw [matrixDirac_sq]
      simp only [Ring.lie_def]
      noncomm_ring
    _ = 0 := hc.lie_eq

end InfoGeometry.OperatorAlgebra.CliffordDirac
