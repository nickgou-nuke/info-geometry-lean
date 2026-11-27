/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The split `Cl(1,1)` operator matrix and its Klein twist

This file proves identities in the full noncommutative matrix rings
`M₂(A)` and `M₂(M₂(B))`.  It proves Clifford generator relations and explicit
reconstruction identities.  It does not assert a universal Clifford-algebra
isomorphism or identify an untyped graded tensor product with a matrix ring.
-/

namespace InfoGeometry.Clifford.Cl11GradedTensorChain

open Matrix

variable {A : Type*} [Ring A]

abbrev Op₂ (A : Type*) := Matrix (Fin 2) (Fin 2) A

def comm {R : Type*} [Ring R] (x y : R) : R := x * y - y * x
def anticomm {R : Type*} [Ring R] (x y : R) : R := x * y + y * x

def sigma : Op₂ A := !![0, 1; 1, 0]
def omega : Op₂ A := !![0, -1; 1, 0]
def gamma : Op₂ A := !![1, 0; 0, -1]
def pPlus : Op₂ A := !![1, 0; 0, 0]
def pMinus : Op₂ A := !![0, 0; 0, 1]

theorem sigma_sq : (sigma : Op₂ A) * sigma = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma]

theorem omega_sq : (omega : Op₂ A) * omega = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [omega]

theorem gamma_sq : (gamma : Op₂ A) * gamma = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [gamma]

theorem sigma_mul_omega : (sigma : Op₂ A) * omega = gamma := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma, omega, gamma]

theorem omega_mul_sigma : (omega : Op₂ A) * sigma = -gamma := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma, omega, gamma]

theorem sigma_omega_anticomm : anticomm (sigma : Op₂ A) omega = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [anticomm, sigma, omega]

theorem gamma_sigma_anticomm : anticomm (gamma : Op₂ A) sigma = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [anticomm, gamma, sigma]

theorem gamma_omega_anticomm : anticomm (gamma : Op₂ A) omega = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [anticomm, gamma, omega]

/-! ## The Klein twist -/

def fiberEmbed (x : A) : Op₂ A := !![x, 0; 0, x]
def kleinTwist (x : A) : Op₂ A := !![x, 0; 0, -x]

theorem kleinTwist_eq_fiberEmbed_mul_gamma (x : A) :
    kleinTwist x = fiberEmbed x * gamma := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, fiberEmbed, gamma]

theorem kleinTwist_mul (x y : A) :
    kleinTwist x * kleinTwist y = fiberEmbed (x * y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, fiberEmbed]

theorem fiberEmbed_mul (x y : A) :
    fiberEmbed x * fiberEmbed y = fiberEmbed (x * y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fiberEmbed]

theorem kleinTwist_anticomm_sigma (x : A) :
    anticomm (kleinTwist x) (sigma : Op₂ A) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anticomm, kleinTwist, sigma]

theorem kleinTwist_anticomm_omega (x : A) :
    anticomm (kleinTwist x) (omega : Op₂ A) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anticomm, kleinTwist, omega]

theorem kleinTwist_comm_gamma (x : A) :
    comm (kleinTwist x) (gamma : Op₂ A) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, kleinTwist, gamma]

theorem kleinTwist_anticomm (x y : A) :
    anticomm (kleinTwist x) (kleinTwist y) = fiberEmbed (anticomm x y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anticomm, kleinTwist, fiberEmbed]

/-! ## Witt ladder and CAR -/

def fPlus : Op₂ A := !![0, 1; 0, 0]
def fMinus : Op₂ A := !![0, 0; 1, 0]

theorem fPlus_eq_peirce : (fPlus : Op₂ A) = pPlus * sigma * pMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fPlus, pPlus, pMinus, sigma]

theorem fMinus_eq_peirce : (fMinus : Op₂ A) = pMinus * sigma * pPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fMinus, pPlus, pMinus, sigma]

theorem fPlus_sq_zero : (fPlus : Op₂ A) * fPlus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [fPlus]

theorem fMinus_sq_zero : (fMinus : Op₂ A) * fMinus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [fMinus]

theorem fPlus_fMinus_anticomm :
    anticomm (fPlus : Op₂ A) fMinus = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anticomm, fPlus, fMinus]

theorem fPlus_fMinus_comm :
    comm (fPlus : Op₂ A) fMinus = gamma := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, fPlus, fMinus, gamma]

theorem kleinTwist_anticomm_fPlus (x : A) :
    anticomm (kleinTwist x) (fPlus : Op₂ A) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anticomm, kleinTwist, fPlus]

theorem kleinTwist_anticomm_fMinus (x : A) :
    anticomm (kleinTwist x) (fMinus : Op₂ A) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anticomm, kleinTwist, fMinus]

/-! ## A relation-lifting result (without an unsupported algebra isomorphism claim) -/

theorem lift_anticommuting_pair
    {x y sx sy : A} (hx : x * x = sx) (hy : y * y = sy)
    (hxy : anticomm x y = 0) :
    (sigma : Op₂ A) * sigma = 1 ∧
    (omega : Op₂ A) * omega = -1 ∧
    kleinTwist x * kleinTwist x = fiberEmbed sx ∧
    kleinTwist y * kleinTwist y = fiberEmbed sy ∧
    anticomm (sigma : Op₂ A) omega = 0 ∧
    anticomm (kleinTwist x) sigma = 0 ∧
    anticomm (kleinTwist y) sigma = 0 ∧
    anticomm (kleinTwist x) omega = 0 ∧
    anticomm (kleinTwist y) omega = 0 ∧
    anticomm (kleinTwist x) (kleinTwist y) = 0 := by
  refine ⟨sigma_sq, omega_sq, ?_, ?_, sigma_omega_anticomm,
    kleinTwist_anticomm_sigma x, kleinTwist_anticomm_sigma y,
    kleinTwist_anticomm_omega x, kleinTwist_anticomm_omega y, ?_⟩
  · rw [kleinTwist_mul, hx]
  · rw [kleinTwist_mul, hy]
  · rw [kleinTwist_anticomm, hxy]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [fiberEmbed]

/-! ## Explicit four-mode reconstruction -/

def kleinFiberLift (x : A) : Op₂ A := kleinTwist x

def modeI (M : Op₂ A) : Op₂ A := fiberEmbed (M 0 0 + M 1 1)
def modeGamma (M : Op₂ A) : Op₂ A := fiberEmbed (M 0 0 - M 1 1)
def modeSigma (M : Op₂ A) : Op₂ A := fiberEmbed (M 0 1 + M 1 0)
def modeOmega (M : Op₂ A) : Op₂ A := fiberEmbed (M 1 0 - M 0 1)

theorem four_mode_reconstruction (M : Op₂ A) :
    modeI M * 1 + modeGamma M * gamma + modeSigma M * sigma +
      modeOmega M * omega = M + M := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [modeI, modeGamma, modeSigma, modeOmega, fiberEmbed,
      gamma, sigma, omega, Matrix.mul_apply,
      Fin.sum_univ_two] <;> noncomm_ring

/-! ## Two recursive stages: relations in the full nested matrix algebra -/

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

section TwoStages

variable {B : Type*} [Ring B]

def jwu1 : NestedMat B := sigma
def jwu2 : NestedMat B := omega
def jwu3 : NestedMat B := kleinTwist sigma
def jwu4 : NestedMat B := kleinTwist omega

theorem nested_four_generator_relations :
    (jwu1 : NestedMat B) * jwu1 = 1 ∧
    (jwu2 : NestedMat B) * jwu2 = -1 ∧
    (jwu3 : NestedMat B) * jwu3 = 1 ∧
    (jwu4 : NestedMat B) * jwu4 = -1 ∧
    anticomm (jwu1 : NestedMat B) jwu2 = 0 ∧
    anticomm (jwu3 : NestedMat B) jwu1 = 0 ∧
    anticomm (jwu4 : NestedMat B) jwu1 = 0 ∧
    anticomm (jwu3 : NestedMat B) jwu2 = 0 ∧
    anticomm (jwu4 : NestedMat B) jwu2 = 0 ∧
    anticomm (jwu3 : NestedMat B) jwu4 = 0 := by
  have h1 : fiberEmbed (1 : Matrix (Fin 2) (Fin 2) B) = 1 := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [fiberEmbed]
  have hm1 : fiberEmbed (-1 : Matrix (Fin 2) (Fin 2) B) = -1 := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [fiberEmbed]
  have h := lift_anticommuting_pair
    (A := Matrix (Fin 2) (Fin 2) B)
    (x := sigma) (y := omega) (sx := 1) (sy := -1)
    sigma_sq omega_sq sigma_omega_anticomm
  rw [h1, hm1] at h
  simpa [jwu1, jwu2, jwu3, jwu4, fiberEmbed] using h

end TwoStages

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) A` for any nontrivial ring `A`. -/
theorem cl11_mat2A_noncomm_exists {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.Clifford.Cl11GradedTensorChain
