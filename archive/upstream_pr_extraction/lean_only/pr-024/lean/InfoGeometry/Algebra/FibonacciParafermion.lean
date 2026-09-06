import Mathlib
import InfoGeometry.Canonical.FibonacciParafermionAtoms
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Canonical.FibonacciParafermionFusionBridge

open Matrix

/-!
# FibonacciParafermion — Real Krein/Majorana/Weyl/sl₂ decomposition

This file adds a representation-theoretic refinement to the existing Fibonacci
anyon formalizations. It decomposes the real Fibonacci F-matrix as:

    F_matrix a b = a • majoranaZ + b • majoranaX
                 = a • sl₂H + b • (sl₂E + sl₂F)

where `majoranaZ`, `majoranaX` are real Majorana/Pauli generators and
`sl₂E`, `sl₂F`, `sl₂H` are the standard 𝔰𝔩₂(ℝ) basis.

This makes explicit that the two-channel Fibonacci recoupling matrix acts
on a real two-component spinor as a reflection-like Majorana operator,
and that the carrier is a real 𝔰𝔩₂ weight module.
-/

namespace FibonacciParafermion

open InfoGeometry.Canonical.FibonacciParafermionAtoms
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-! ## 1. Real Krein space data -/

/-- Krein fundamental symmetry `diag(1, -1)`. -/
def kreinJ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Krein indefinite inner product `⟨v,w⟩_J = v₀w₀ - v₁w₁`. -/
def kreinForm (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 - v 1 * w 1

/-- Krein adjoint `A⁺ = J Aᵀ J`. -/
def kreinAdjoint (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinJ * A.transpose * kreinJ

/-! ## 2. Real Majorana/Clifford generators -/

/-- Majorana `σ_x` (real, symmetric, involutive). -/
def majoranaX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Majorana `σ_z` (real, symmetric, involutive). -/
def majoranaZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem majoranaX_sq : majoranaX * majoranaX = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [majoranaX, Matrix.mul_apply, Fin.sum_univ_two]

theorem majoranaZ_sq : majoranaZ * majoranaZ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [majoranaZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem majoranaX_majoranaZ_anticomm : majoranaX * majoranaZ + majoranaZ * majoranaX = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [majoranaX, majoranaZ]

theorem majoranaZ_krein_self_adjoint : kreinAdjoint majoranaZ = majoranaZ := by
  have hT : majoranaZ.transpose = majoranaZ := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [majoranaZ]
  calc
    kreinAdjoint majoranaZ = kreinJ * majoranaZ * kreinJ := by
      simp [kreinAdjoint, hT]
    _ = majoranaZ := by
      ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [kreinJ, majoranaZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem majoranaX_krein_skew_adjoint : kreinAdjoint majoranaX = -majoranaX := by
  have hT : majoranaX.transpose = majoranaX := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [majoranaX]
  calc
    kreinAdjoint majoranaX = kreinJ * majoranaX * kreinJ := by
      simp [kreinAdjoint, hT]
    _ = -majoranaX := by
      ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [kreinJ, majoranaX, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 3. F-matrix as a Majorana unit -/

theorem F_matrix_majorana_decomposition (a b : ℝ) : F_matrix a b = a • majoranaZ + b • majoranaX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [F_matrix, majoranaX, majoranaZ]

theorem F_matrix_is_real_majorana_unit (a b : ℝ) (h : IsFibonacciRelation a b) :
    (a • majoranaZ + b • majoranaX) * (a • majoranaZ + b • majoranaX) = 1 := by
  rw [← F_matrix_majorana_decomposition]; exact F_matrix_sq a b h

/-! ## 4. Real Weyl projectors (Dirac splitting) -/

def WeylPlusProjector : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def WeylMinusProjector : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

theorem WeylPlusProjector_sq : WeylPlusProjector * WeylPlusProjector = WeylPlusProjector := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [WeylPlusProjector, Matrix.mul_apply, Fin.sum_univ_two]

theorem WeylMinusProjector_sq : WeylMinusProjector * WeylMinusProjector = WeylMinusProjector := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [WeylMinusProjector, Matrix.mul_apply, Fin.sum_univ_two]

theorem WeylProjectors_sum : WeylPlusProjector + WeylMinusProjector = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [WeylPlusProjector, WeylMinusProjector]

theorem WeylProjectors_orthogonal :
    WeylPlusProjector * WeylMinusProjector = 0 ∧ WeylMinusProjector * WeylPlusProjector = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [WeylPlusProjector, WeylMinusProjector, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 5. Real 𝔰𝔩₂(ℝ) representation -/

def sl₂E : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def sl₂F : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
def sl₂H : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def commutator (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := A * B - B * A

theorem sl₂H_eq_majoranaZ : sl₂H = majoranaZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sl₂H, majoranaZ]

theorem sl₂_relation_H_E : commutator sl₂H sl₂E = 2 • sl₂E := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [commutator, sl₂H, sl₂E]

theorem sl₂_relation_H_F : commutator sl₂H sl₂F = (-2 : ℝ) • sl₂F := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [commutator, sl₂H, sl₂F]

theorem sl₂_relation_E_F : commutator sl₂E sl₂F = sl₂H := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [commutator, sl₂E, sl₂F, sl₂H]

theorem WeylPlus_has_H_weight_plus : sl₂H * WeylPlusProjector = WeylPlusProjector := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [sl₂H, WeylPlusProjector]

theorem WeylMinus_has_H_weight_minus : sl₂H * WeylMinusProjector = -WeylMinusProjector := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [sl₂H, WeylMinusProjector]

theorem sl₂E_raises_minus_to_plus : WeylPlusProjector * sl₂E * WeylMinusProjector = sl₂E := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [WeylPlusProjector, WeylMinusProjector, sl₂E]

theorem sl₂F_lowers_plus_to_minus : WeylMinusProjector * sl₂F * WeylPlusProjector = sl₂F := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [WeylPlusProjector, WeylMinusProjector, sl₂F]

theorem majoranaX_is_sl₂_off_diagonal : majoranaX = sl₂E + sl₂F := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [majoranaX, sl₂E, sl₂F]

theorem F_matrix_sl₂_decomposition (a b : ℝ) : F_matrix a b = a • sl₂H + b • (sl₂E + sl₂F) := by
  rw [sl₂H_eq_majoranaZ, ← majoranaX_is_sl₂_off_diagonal]; exact F_matrix_majorana_decomposition a b

/-! ## 6. F-matrix action on spinors -/

abbrev RealDiracSpinor := Fin 2 → ℝ

def F_action (a b : ℝ) (v : RealDiracSpinor) : RealDiracSpinor := (F_matrix a b).mulVec v

theorem F_action_apply (a b cPlus cMinus : ℝ) : F_action a b ![cPlus, cMinus] =
    ![a * cPlus + b * cMinus, b * cPlus - a * cMinus] := by
  ext i; fin_cases i <;> simp [F_action, F_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem F_action_involutive (a b : ℝ) (h : IsFibonacciRelation a b) (v : RealDiracSpinor) :
    F_action a b (F_action a b v) = v := by
  calc
    F_action a b (F_action a b v) = ((F_matrix a b * F_matrix a b).mulVec v) := by
      simp [F_action, Matrix.mulVec_mulVec]
    _ = (1 : Matrix (Fin 2) (Fin 2) ℝ).mulVec v := by rw [F_matrix_sq a b h]
    _ = v := by simp

theorem F_matrix_real_krein_majorana_sl2_picture (a b : ℝ) (h : IsFibonacciRelation a b) :
    F_matrix a b * F_matrix a b = 1 ∧
    F_matrix a b = a • majoranaZ + b • majoranaX ∧
    F_matrix a b = a • sl₂H + b • (sl₂E + sl₂F) := by
  exact ⟨F_matrix_sq a b h, F_matrix_majorana_decomposition a b, F_matrix_sl₂_decomposition a b⟩

end FibonacciParafermion
