import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.MatrixFourierSL2Representation

open Matrix Complex

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

-- 1. Explicit diagonal operator with eigenvalues 0, 1, -1, I, -I.
def fourierMatrix5 : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal ![(0 : ℂ), 1, -1, Complex.I, -Complex.I]

theorem fourierMatrix5_quintic :
    fourierMatrix5 ^ 5 = fourierMatrix5 := by
  have hnegI4 : (-Complex.I) ^ 4 = 1 := by
    norm_num [Complex.I_sq]
  unfold fourierMatrix5
  rw [Matrix.diagonal_pow]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i
  · norm_num
  · norm_num
  · norm_num
  · norm_num [Complex.I_sq]
  · change (-Complex.I) ^ 5 = -Complex.I
    rw [pow_succ', hnegI4, mul_one]

-- 2. Explicit Projectors for the 5x5 Fourier Matrix
def P_vac5 : Matrix (Fin 5) (Fin 5) ℂ := 1 - fourierMatrix5 ^ 4
def P_sym5 : Matrix (Fin 5) (Fin 5) ℂ := (1 / 2 : ℂ) • (fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2)
def P_anti5 : Matrix (Fin 5) (Fin 5) ℂ := (1 / 2 : ℂ) • (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2)

theorem fourier5_projector_completeness :
    P_vac5 + P_sym5 + P_anti5 = 1 := by
  simp only [P_vac5, P_sym5, P_anti5]
  module

theorem fourierMatrix5_pow_eight :
    fourierMatrix5 ^ 8 = fourierMatrix5 ^ 4 := by
  calc
    fourierMatrix5 ^ 8 = fourierMatrix5 ^ 5 * fourierMatrix5 ^ 3 := by
      rw [← pow_add]
    _ = fourierMatrix5 * fourierMatrix5 ^ 3 := by
      rw [fourierMatrix5_quintic]
    _ = fourierMatrix5 ^ 4 := by
      rw [← pow_succ']

theorem fourierMatrix5_power_product_zero :
    (fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2) *
        (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2) = 0 := by
  calc
    (fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2) *
        (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2) =
      fourierMatrix5 ^ 8 - fourierMatrix5 ^ 4 := by noncomm_ring
    _ = 0 := by rw [fourierMatrix5_pow_eight]; simp

theorem fourier5_projector_orthogonality :
    P_sym5 * P_anti5 = 0 := by
  change ((1 / 2 : ℂ) • (fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2)) *
      ((1 / 2 : ℂ) • (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2)) = 0
  rw [show ((1 / 2 : ℂ) • (fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2)) *
      ((1 / 2 : ℂ) • (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2)) =
      (1 / 4 : ℂ) • ((fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2) *
        (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2)) by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num]
  rw [fourierMatrix5_power_product_zero]
  simp

-- 3. Explicit 2x2 SL(2, ℂ) Matrix Generators
def sl2_e : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 0, 0]

def sl2_f : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 0; 1, 0]

def sl2_h : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

def commutator (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A * B - B * A

theorem sl2_comm_h_e :
    commutator sl2_h sl2_e = (2 : ℂ) • sl2_e := by
  unfold commutator sl2_h sl2_e
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

theorem sl2_comm_h_f :
    commutator sl2_h sl2_f = -((2 : ℂ) • sl2_f) := by
  unfold commutator sl2_h sl2_f
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

theorem sl2_comm_e_f :
    commutator sl2_e sl2_f = sl2_h := by
  unfold commutator sl2_e sl2_f sl2_h
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

def sl2_casimir : Matrix (Fin 2) (Fin 2) ℂ :=
  sl2_e * sl2_f + sl2_f * sl2_e + (1 / 2 : ℂ) • (sl2_h * sl2_h)

theorem sl2_casimir_scalar :
    sl2_casimir = (3 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold sl2_casimir sl2_e sl2_f sl2_h
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

theorem sl2_casimir_comm_e :
    commutator sl2_casimir sl2_e = 0 := by
  rw [sl2_casimir_scalar]
  unfold commutator
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end

end InfoGeometry.Quantum.MatrixFourierSL2Representation
