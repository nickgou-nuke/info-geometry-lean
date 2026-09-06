import InfoGeometry.Clifford.SplitQuaternionNilpotentFlow
import InfoGeometry.Canonical.CantorLocalCl11HopParity

import Mathlib.Tactic

set_option autoImplicit false

/-!
# Split-quaternion nilpotent flow and the local chiral CAR atom

This owner records the exact convention used by `SplitQuaternion.toMatrix`.
With that representation the split-quaternion generator `i - j` is the
lower-left nilpotent, so it corresponds to creation rather than annihilation.
The opposite null direction is the upper-right nilpotent.

The file deliberately treats the split-quaternion product and matrix
composition as separate products; it only transports the already proved
coordinate identities through the explicit matrix readout.
-/

namespace InfoGeometry.Clifford.SplitQuaternionNilpotentChiralCARBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.SplitQuaternionNilpotentFlow
open InfoGeometry.Canonical.SplitCliffordCantorFock
open InfoGeometry.Canonical.CantorLocalCl11HopParity

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-! ## The two null directions in the canonical matrix convention -/

def N_plus : SplitQuaternion := N_nil

def N_minus : SplitQuaternion := ⟨0, 1, 1, 0⟩

def rho (q : SplitQuaternion) : M2R := toMatrix q

@[simp] theorem rho_N_plus : rho N_plus = (-2 : ℝ) • aDag_op := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, N_plus, N_nil, toMatrix, aDag_op, Matrix.smul_apply] <;> norm_num

@[simp] theorem rho_N_minus : rho N_minus = 2 • a_op := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, N_minus, toMatrix, a_op, Matrix.smul_apply] <;> norm_num

@[simp] theorem N_plus_sq : N_plus * N_plus = 0 := N_nil_sq

theorem rho_N_plus_sq : rho N_plus * rho N_plus = 0 := by
  rw [rho_N_plus]
  simp [aDag_op_sq_zero]

theorem rho_N_minus_sq : rho N_minus * rho N_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho, N_minus, toMatrix, a_op, Matrix.mul_apply,
      Fin.sum_univ_two]

/-! ## Exact unipotent flow -/

def rhoFlow (T : ℝ) : M2R := rho (sq_nilpotent_exp T)

theorem rhoFlow_eq_one_add (T : ℝ) :
    rhoFlow T = (1 : M2R) + T • rho N_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoFlow, rho, sq_nilpotent_exp_eq, N_plus, N_nil, toMatrix,
      Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem rhoFlow_eq_creation (T : ℝ) :
    rhoFlow T = (1 : M2R) - (2 * T) • aDag_op := by
  rw [rhoFlow_eq_one_add, rho_N_plus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem rhoFlow_eq_annihilation (T : ℝ) :
    rho (⟨1, -T, -T, 0⟩ : SplitQuaternion) =
      (1 : M2R) - (2 * T) • a_op := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, toMatrix, a_op, Matrix.one_apply, Matrix.add_apply,
      Matrix.smul_apply] <;> ring

theorem rhoFlow_mul (S T : ℝ) :
    rhoFlow S * rhoFlow T = rhoFlow (S + T) := by
  rw [rhoFlow_eq_creation, rhoFlow_eq_creation, rhoFlow_eq_creation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aDag_op, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rhoFlow_inverse (T : ℝ) :
    rhoFlow T * ((1 : M2R) + (2 * T) • aDag_op) = 1 := by
  rw [rhoFlow_eq_creation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aDag_op, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ## The local split-Clifford packet -/

theorem parity_commutator_annihilation :
    localParityOperator * a_op - a_op * localParityOperator = 2 • a_op := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localParityOperator, localVacuumProjection,
      localOccupiedProjection, a_op, aDag_op, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem parity_commutator_creation :
    localParityOperator * aDag_op - aDag_op * localParityOperator =
      -(2 : ℝ) • aDag_op := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localParityOperator, localVacuumProjection,
      localOccupiedProjection, a_op, aDag_op, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem nilpotent_canonical_packet :
    rho N_plus = (-2 : ℝ) • aDag_op ∧
      rho N_minus = 2 • a_op ∧
      localParityOperator * a_op - a_op * localParityOperator = 2 • a_op ∧
      localParityOperator * aDag_op - aDag_op * localParityOperator =
        -(2 : ℝ) • aDag_op := by
  exact ⟨rho_N_plus, rho_N_minus, parity_commutator_annihilation,
    parity_commutator_creation⟩

end InfoGeometry.Clifford.SplitQuaternionNilpotentChiralCARBridge
