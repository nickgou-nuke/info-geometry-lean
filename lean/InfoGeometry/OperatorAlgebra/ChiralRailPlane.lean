import Mathlib.Tactic
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

variable {R : Type*} [CommRing R]

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
structure ChiralRailPlane (R : Type*) [CommRing R] where
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

theorem metric_compatibility_standard : K_standard.transpose * g_standard * K_standard = (g_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K_standard, g_standard, Matrix.mul_apply, Fin.sum_univ_two]

theorem symplectic_compatibility_standard : K_standard.transpose * Ω_standard * K_standard = (Ω_standard : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K_standard, Ω_standard, Matrix.mul_apply, Fin.sum_univ_two]

def standardChiralRailPlane (R : Type*) [CommRing R] : ChiralRailPlane R where
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

/-- The canonical embedding into the Zorn split-octonion basis. -/
def toZornBasis (i : Fin 3) : ZornVectorMatrix R :=
  ZornVectorMatrix.U i

end InfoGeometry.OperatorAlgebra.ChiralRailPlane
