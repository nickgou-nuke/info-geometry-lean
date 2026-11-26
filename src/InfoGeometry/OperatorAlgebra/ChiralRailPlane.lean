/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.OperatorAlgebra.ChiralRailPlane

The local polarized Cl(1,1)/CAR cell sharing the global idempotents u_±.

The circular operator algebra with:
- complex structure K (K^2 = -1)
- idempotent projectors P_± (P_±^2 = P_±)
- nilpotent raising/lowering operators E_R, E_L (E_{R/L}^2 = 0)
- commutator [E_R, E_L] = Γ
- anticommutator {E_R, E_L} = 1
- metric compatibility Kᵀ g K = g, Kᵀ Ω K = Ω

All relations are verified with native Mathlib proofs and zero `sorry`s.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralRailPlane

open InfoGeometry.Algebra
open ZornVectorMatrix
open Matrix

variable {R : Type*} [Ring R]

def K_standard : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]
def P_plus_standard : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]
def P_minus_standard : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]
def E_R_standard : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
def E_L_standard : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]
def Γ_standard : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
def Ω_standard : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
def g_standard : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 1]

/-- A chiral rail plane is a 4-dimensional real vector space with
    algebraic structure, projectors, raising/lowering operators, and metric. -/
structure ChiralRailPlane (R : Type*) [Ring R] where
  K : Matrix (Fin 2) (Fin 2) R
  P_plus : Matrix (Fin 2) (Fin 2) R
  P_minus : Matrix (Fin 2) (Fin 2) R
  E_R : Matrix (Fin 2) (Fin 2) R
  E_L : Matrix (Fin 2) (Fin 2) R
  Γ : Matrix (Fin 2) (Fin 2) R
  Ω : Matrix (Fin 2) (Fin 2) R
  g : Matrix (Fin 2) (Fin 2) R
  h_K_sq : K * K = -(1 : Matrix (Fin 2) (Fin 2) R)
  h_P_plus_idempotent : P_plus * P_plus = P_plus
  h_P_minus_idempotent : P_minus * P_minus = P_minus
  h_P_plus_orthogonal : P_plus * P_minus = 0
  h_P_complete : P_plus + P_minus = 1
  h_E_R_nilpotent : E_R * E_R = 0
  h_E_L_nilpotent : E_L * E_L = 0
  h_commutator : E_R * E_L - E_L * E_R = Γ
  h_anticommutator : E_R * E_L + E_L * E_R = 1
  h_metric_compat : K.transpose * g * K = g
  h_symplectic_compat : K.transpose * Ω * K = Ω

theorem K_sq_standard : K_standard * K_standard = -(1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_plus_idempotent_standard : P_plus_standard * P_plus_standard = (P_plus_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_plus_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_minus_idempotent_standard : P_minus_standard * P_minus_standard = (P_minus_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_minus_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_plus_orthogonal_standard : P_plus_standard * P_minus_standard = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_plus_standard, P_minus_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_complete_standard : P_plus_standard + P_minus_standard = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_plus_standard, P_minus_standard]

theorem E_R_nilpotent_standard : E_R_standard * E_R_standard = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E_R_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_L_nilpotent_standard : E_L_standard * E_L_standard = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E_L_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem commutator_E_R_E_L_standard : E_R_standard * E_L_standard - E_L_standard * E_R_standard = (Γ_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E_R_standard, E_L_standard, Γ_standard]

theorem anticommutator_E_R_E_L_standard : E_R_standard * E_L_standard + E_L_standard * E_R_standard = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E_R_standard, E_L_standard]

theorem E_R_E_L_noncomm [Nontrivial R] :
    (E_R_standard : Matrix (Fin 2) (Fin 2) R) * E_L_standard ≠
      E_L_standard * E_R_standard := by
  intro h
  have h00 : (1 : R) = 0 := by
    simpa [E_R_standard, E_L_standard, Matrix.mul_apply, Fin.sum_univ_two] using
      congr_fun (congr_fun h 0) 0
  exact one_ne_zero h00

theorem metric_compatibility_standard : K_standard.transpose * g_standard * K_standard = (g_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K_standard, g_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem symplectic_compatibility_standard : K_standard.transpose * Ω_standard * K_standard = (Ω_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K_standard, Ω_standard, Matrix.mul_apply, Fin.sum_univ_two]

def standardChiralRailPlane (R : Type*) [Ring R] : ChiralRailPlane R where
  K := K_standard
  P_plus := P_plus_standard
  P_minus := P_minus_standard
  E_R := E_R_standard
  E_L := E_L_standard
  Γ := Γ_standard
  Ω := Ω_standard
  g := g_standard
  h_K_sq := K_sq_standard
  h_P_plus_idempotent := P_plus_idempotent_standard
  h_P_minus_idempotent := P_minus_idempotent_standard
  h_P_plus_orthogonal := P_plus_orthogonal_standard
  h_P_complete := P_complete_standard
  h_E_R_nilpotent := E_R_nilpotent_standard
  h_E_L_nilpotent := E_L_nilpotent_standard
  h_commutator := commutator_E_R_E_L_standard
  h_anticommutator := anticommutator_E_R_E_L_standard
  h_metric_compat := metric_compatibility_standard
  h_symplectic_compat := symplectic_compatibility_standard

instance (B : Type*) [Ring B] : Inhabited (ChiralRailPlane B) := ⟨standardChiralRailPlane B⟩

/-- The canonical embedding into the Zorn split-octonion basis. -/
def toZornBasis (i : Fin 3) : ZornVectorMatrix R :=
  ZornVectorMatrix.U i

/-- The odd chiral combination of the two nilpotent ladder operators. -/
def chiralDifference (plane : ChiralRailPlane R) : Matrix (Fin 2) (Fin 2) R :=
  plane.E_R - plane.E_L

/-- The even chiral combination of the two nilpotent ladder operators. -/
def chiralSum (plane : ChiralRailPlane R) : Matrix (Fin 2) (Fin 2) R :=
  plane.E_R + plane.E_L

/-- The odd combination squares to the negative identity. -/
theorem chiral_difference_sq (plane : ChiralRailPlane R) :
    chiralDifference plane * chiralDifference plane =
      -(1 : Matrix (Fin 2) (Fin 2) R) := by
  unfold chiralDifference
  simp only [_root_.sub_mul, _root_.mul_sub, plane.h_E_R_nilpotent,
    plane.h_E_L_nilpotent]
  rw [← plane.h_anticommutator]
  abel

/-- The even combination squares to the identity. -/
theorem chiral_sum_sq (plane : ChiralRailPlane R) :
    chiralSum plane * chiralSum plane =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  unfold chiralSum
  simp only [_root_.add_mul, _root_.mul_add, plane.h_E_R_nilpotent,
    plane.h_E_L_nilpotent]
  calc
    0 + plane.E_L * plane.E_R + (plane.E_R * plane.E_L + 0) =
        plane.E_R * plane.E_L + plane.E_L * plane.E_R := by abel
    _ = 1 := plane.h_anticommutator

/-- The ordered products of the two combinations recover the commutator,
with the order determining its sign. -/
theorem chiral_sum_mul_difference (plane : ChiralRailPlane R) :
    chiralSum plane * chiralDifference plane = -plane.Γ := by
  unfold chiralSum chiralDifference
  simp only [_root_.add_mul, _root_.mul_sub, plane.h_E_R_nilpotent,
    plane.h_E_L_nilpotent]
  calc
    0 + plane.E_L * plane.E_R - (plane.E_R * plane.E_L + 0) =
        -(plane.E_R * plane.E_L - plane.E_L * plane.E_R) := by abel
    _ = -plane.Γ := by rw [plane.h_commutator]

/-- The reverse ordered product recovers the chiral commutator. -/
theorem chiral_difference_mul_sum (plane : ChiralRailPlane R) :
    chiralDifference plane * chiralSum plane = plane.Γ := by
  unfold chiralDifference chiralSum
  simp only [_root_.sub_mul, _root_.mul_add, plane.h_E_R_nilpotent,
    plane.h_E_L_nilpotent]
  calc
    0 - plane.E_L * plane.E_R + (plane.E_R * plane.E_L - 0) =
        plane.E_R * plane.E_L - plane.E_L * plane.E_R := by abel
    _ = plane.Γ := plane.h_commutator

end InfoGeometry.OperatorAlgebra.ChiralRailPlane
