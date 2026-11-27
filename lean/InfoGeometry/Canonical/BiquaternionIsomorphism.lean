/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Canonical.BiquaternionSU2
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Biquaternion Algebra Isomorphism

This module constructs the explicit `ℂ`-algebra isomorphism
`biquaternionAlgEquivMat2 : Quaternion ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ`
between the complexified quaternions (biquaternions) and `2 × 2` complex
matrices, reusing `InfoGeometry.Canonical.Biquaternions` (`Qi`, `Qj`, `Qk`)
and `InfoGeometry.Algebra.FiniteSpin.Mat2C`.

It proves that the matrix determinant equals the quaternion norm squared
`Quaternion.normSq q = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2`,
records the images of the pure quaternion basis units `(Qi, Qj, Qk)` as
`(I • σ₃, I • σ₂, I • σ₁)` (noting that `LorentzBiquaternionEquivalence`
uses a cyclic permutation of these generators), and provides explicit
non-commutativity witnesses.
-/

noncomputable section

namespace InfoGeometry.Canonical.BiquaternionIsomorphism

open Matrix Complex
open InfoGeometry.Canonical.Biquaternions

/-- The biquaternion algebra carrier `Quaternion ℂ`. -/
abbrev Biquaternion := InfoGeometry.Canonical.Biquaternions.Biquaternion

/-- The complex `2 × 2` matrix carrier `Matrix (Fin 2) (Fin 2) ℂ`. -/
abbrev M2 := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Explicit `ℂ`-algebra embedding of biquaternions into `2 × 2` complex matrices. -/
def ψ (q : Quaternion ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![q.re + q.imI * I, q.imJ + q.imK * I;
     -q.imJ + q.imK * I, q.re - q.imI * I]

/-- Explicit inverse map from `2 × 2` complex matrices to biquaternions. -/
def ψInv (M : Matrix (Fin 2) (Fin 2) ℂ) : Quaternion ℂ :=
  ⟨(M 0 0 + M 1 1) / 2,
   -I * (M 0 0 - M 1 1) / 2,
   (M 0 1 - M 1 0) / 2,
   -I * (M 0 1 + M 1 0) / 2⟩

theorem ψ_zero : ψ 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ψ]

theorem ψ_one : ψ 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ψ]

theorem ψ_add (q₁ q₂ : Quaternion ℂ) : ψ (q₁ + q₂) = ψ q₁ + ψ q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [ψ]; ring)

theorem ψ_mul (q₁ q₂ : Quaternion ℂ) : ψ (q₁ * q₂) = ψ q₁ * ψ q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ψ, Matrix.mul_apply, Fin.sum_univ_two]
     ring_nf
     simp [pow_two, Complex.I_mul_I]
     try ring)

theorem ψ_commutes (c : ℂ) :
    ψ (algebraMap ℂ (Quaternion ℂ) c) = algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ψ, Matrix.algebraMap_matrix_apply]

theorem ψInv_ψ (q : Quaternion ℂ) : ψInv (ψ q) = q := by
  ext <;> simp [ψInv, ψ] <;> ring_nf <;> simp [pow_two, Complex.I_mul_I]

theorem ψ_ψInv (M : Matrix (Fin 2) (Fin 2) ℂ) : ψ (ψInv M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ψ, ψInv]; ring_nf; simp [pow_two, Complex.I_mul_I]; ring)

/-- Explicit `ℂ`-algebra equivalence `Quaternion ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ`. -/
def biquaternionAlgEquivMat2 : Quaternion ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := ψ
  invFun := ψInv
  left_inv := ψInv_ψ
  right_inv := ψ_ψInv
  map_mul' := ψ_mul
  map_add' := ψ_add
  commutes' := ψ_commutes

@[simp]
theorem biquaternionAlgEquivMat2_apply (q : Quaternion ℂ) :
    biquaternionAlgEquivMat2 q = ψ q :=
  rfl

@[simp]
theorem biquaternionAlgEquivMat2_symm_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    biquaternionAlgEquivMat2.symm M = ψInv M :=
  rfl

theorem biquaternionAlgEquivMat2_Qi :
    biquaternionAlgEquivMat2 Qi = !![I, 0; 0, -I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ψ, Qi]

theorem biquaternionAlgEquivMat2_Qj :
    biquaternionAlgEquivMat2 Qj = !![(0 : ℂ), 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ψ, Qj]

theorem biquaternionAlgEquivMat2_Qk :
    biquaternionAlgEquivMat2 Qk = !![(0 : ℂ), I; I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ψ, Qk]

theorem det_ψ_eq_norm_sq (q : Quaternion ℂ) :
    Matrix.det (ψ q) = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  rw [ψ, Matrix.det_fin_two_of]
  ring_nf
  simp [pow_two, Complex.I_mul_I]
  ring

theorem det_biquaternionAlgEquivMat2_eq_normSq (q : Quaternion ℂ) :
    Matrix.det (biquaternionAlgEquivMat2 q) = Quaternion.normSq q := by
  rw [biquaternionAlgEquivMat2_apply, det_ψ_eq_norm_sq, Quaternion.normSq_def']

theorem det_biquaternionAlgEquivMat2_mul (p q : Quaternion ℂ) :
    Matrix.det (biquaternionAlgEquivMat2 (p * q)) =
      Quaternion.normSq p * Quaternion.normSq q := by
  rw [map_mul, Matrix.det_mul,
    det_biquaternionAlgEquivMat2_eq_normSq, det_biquaternionAlgEquivMat2_eq_normSq]

/-- Matrix image of `Qi` under `biquaternionAlgEquivMat2`. -/
def matI : Matrix (Fin 2) (Fin 2) ℂ := biquaternionAlgEquivMat2 Qi

/-- Matrix image of `Qj` under `biquaternionAlgEquivMat2`. -/
def matJ : Matrix (Fin 2) (Fin 2) ℂ := biquaternionAlgEquivMat2 Qj

/-- Matrix image of `Qk` under `biquaternionAlgEquivMat2`. -/
def matK : Matrix (Fin 2) (Fin 2) ℂ := biquaternionAlgEquivMat2 Qk

theorem matI_mul_matJ_eq_matK : matI * matJ = matK := by
  change biquaternionAlgEquivMat2 Qi * biquaternionAlgEquivMat2 Qj =
    biquaternionAlgEquivMat2 Qk
  rw [← map_mul]
  congr 1
  ext <;> simp [Qi, Qj, Qk]

theorem biquaternion_noncomm : Qi * Qj ≠ Qj * Qi := by
  intro h
  have h0 : (Qi * Qj).imK = (Qj * Qi).imK :=
    congrArg (fun q : Quaternion ℂ => q.imK) h
  simp [Qi, Qj] at h0
  norm_num at h0

theorem matI_mul_matJ_ne : matI * matJ ≠ matJ * matI := by
  intro h
  apply biquaternion_noncomm
  apply biquaternionAlgEquivMat2.injective
  simpa [matI, matJ, map_mul] using h

theorem mat2C_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨matI, matJ, matI_mul_matJ_ne⟩

end InfoGeometry.Canonical.BiquaternionIsomorphism
