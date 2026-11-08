import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

/-!
# Coquaternion basis calculations for `2 × 2` matrices

This file proves a basis expansion and a matrix anticommutator consequence over
a commutative ring in which `2` is invertible. These are finite matrix
identities; the file does not define a differential operator or manifold.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition

open Matrix

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

def matOne : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 1]
def matI : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]
def matJ : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
def matK : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

def extractD0 (M : Matrix (Fin 2) (Fin 2) R) : R := ⅟(2 : R) * (M 0 0 + M 1 1)
def extractDJ (M : Matrix (Fin 2) (Fin 2) R) : R := ⅟(2 : R) * (M 0 0 - M 1 1)
def extractDI (M : Matrix (Fin 2) (Fin 2) R) : R := ⅟(2 : R) * (M 1 0 - M 0 1)
def extractDK (M : Matrix (Fin 2) (Fin 2) R) : R := ⅟(2 : R) * (M 1 0 + M 0 1)

theorem coquaternionic_expansion (M : Matrix (Fin 2) (Fin 2) R) :
    M = (extractD0 M) • matOne + (extractDI M) • matI +
        (extractDJ M) • matJ + (extractDK M) • matK := by
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [extractD0, extractDI, extractDJ, extractDK, matOne, matI, matJ, matK]
    have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    calc
      M 0 0 = 1 * M 0 0 := by ring
      _ = (⅟(2:R) * 2) * M 0 0 := by rw [h2]
      _ = ⅟(2:R)*(M 0 0 + M 1 1)*1 + ⅟(2:R)*(M 1 0 - M 0 1)*0 + ⅟(2:R)*(M 0 0 - M 1 1)*1 + ⅟(2:R)*(M 1 0 + M 0 1)*0 := by ring
  · dsimp [extractD0, extractDI, extractDJ, extractDK, matOne, matI, matJ, matK]
    have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    calc
      M 0 1 = 1 * M 0 1 := by ring
      _ = (⅟(2:R) * 2) * M 0 1 := by rw [h2]
      _ = ⅟(2:R)*(M 0 0 + M 1 1)*0 + ⅟(2:R)*(M 1 0 - M 0 1)*(-1) + ⅟(2:R)*(M 0 0 - M 1 1)*0 + ⅟(2:R)*(M 1 0 + M 0 1)*1 := by ring
  · dsimp [extractD0, extractDI, extractDJ, extractDK, matOne, matI, matJ, matK]
    have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    calc
      M 1 0 = 1 * M 1 0 := by ring
      _ = (⅟(2:R) * 2) * M 1 0 := by rw [h2]
      _ = ⅟(2:R)*(M 0 0 + M 1 1)*0 + ⅟(2:R)*(M 1 0 - M 0 1)*1 + ⅟(2:R)*(M 0 0 - M 1 1)*0 + ⅟(2:R)*(M 1 0 + M 0 1)*1 := by ring
  · dsimp [extractD0, extractDI, extractDJ, extractDK, matOne, matI, matJ, matK]
    have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    calc
      M 1 1 = 1 * M 1 1 := by ring
      _ = (⅟(2:R) * 2) * M 1 1 := by rw [h2]
      _ = ⅟(2:R)*(M 0 0 + M 1 1)*1 + ⅟(2:R)*(M 1 0 - M 0 1)*0 + ⅟(2:R)*(M 0 0 - M 1 1)*(-1) + ⅟(2:R)*(M 1 0 + M 0 1)*0 := by ring

theorem chiral_anticommutation_reduction (D : Matrix (Fin 2) (Fin 2) R)
    (h_chiral : D * matJ + matJ * D = 0) :
    extractD0 D = 0 ∧ extractDJ D = 0 := by
  have h00 : (D * matJ + matJ * D : Matrix (Fin 2) (Fin 2) R) 0 0 = 0 := congr_arg (fun (M : Matrix (Fin 2) (Fin 2) R) => M 0 0) h_chiral
  have h11 : (D * matJ + matJ * D : Matrix (Fin 2) (Fin 2) R) 1 1 = 0 := congr_arg (fun (M : Matrix (Fin 2) (Fin 2) R) => M 1 1) h_chiral

  have h_D00 : D 0 0 = 0 := by
    have h_eval : (D * matJ + matJ * D : Matrix (Fin 2) (Fin 2) R) 0 0 = 2 * D 0 0 := by
      dsimp [matJ, Matrix.mul_apply, dotProduct]; simp; ring
    rw [h_eval] at h00
    have h_inv : ⅟(2:R) * (2 * D 0 0) = ⅟(2:R) * 0 := by rw [h00]
    rw [← mul_assoc, invOf_mul_self, one_mul, mul_zero] at h_inv
    exact h_inv
  have h_D11 : D 1 1 = 0 := by
    have h_eval : (D * matJ + matJ * D : Matrix (Fin 2) (Fin 2) R) 1 1 = -2 * D 1 1 := by
      dsimp [matJ, Matrix.mul_apply, dotProduct]; simp; ring
    rw [h_eval] at h11
    have h_inv : -⅟(2:R) * (-2 * D 1 1) = -⅟(2:R) * 0 := by rw [h11]
    have h_simp : -⅟(2:R) * (-2 * D 1 1) = (⅟(2:R) * 2) * D 1 1 := by ring
    rw [h_simp, invOf_mul_self, one_mul, mul_zero] at h_inv
    exact h_inv
  constructor
  · dsimp [extractD0]; rw [h_D00, h_D11, add_zero, mul_zero]
  · dsimp [extractDJ]; rw [h_D00, h_D11, sub_zero, mul_zero]

theorem dirac_chiral_collapse (D : Matrix (Fin 2) (Fin 2) R)
    (h_chiral : D * matJ + matJ * D = 0) :
    D = (extractDI D) • matI + (extractDK D) • matK := by
  have h_exp := coquaternionic_expansion D
  have ⟨h_d0, h_dj⟩ := chiral_anticommutation_reduction D h_chiral
  rw [h_d0, h_dj] at h_exp
  simp only [zero_smul, zero_add, add_zero] at h_exp
  exact h_exp

end InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
