import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
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

-- 1. Explicit 5x5 Fourier Matrix Generator with eigenvalues 0, 1, -1, i, -i
def fourierMatrix5 : Matrix (Fin 5) (Fin 5) ℂ :=
  ![![0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0],
    ![0, 0, -1, 0, 0],
    ![0, 0, 0, Complex.I, 0],
    ![0, 0, 0, 0, -Complex.I]]

theorem fourierMatrix5_quintic :
    fourierMatrix5 ^ 5 = fourierMatrix5 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMatrix5, Matrix.mul_apply, pow_succ, Fin.sum_univ_five]

-- 2. Explicit Projectors for the 5x5 Fourier Matrix
def P_vac5 : Matrix (Fin 5) (Fin 5) ℂ := 1 - fourierMatrix5 ^ 4
def P_sym5 : Matrix (Fin 5) (Fin 5) ℂ := (1 / 2 : ℂ) • (fourierMatrix5 ^ 4 + fourierMatrix5 ^ 2)
def P_anti5 : Matrix (Fin 5) (Fin 5) ℂ := (1 / 2 : ℂ) • (fourierMatrix5 ^ 4 - fourierMatrix5 ^ 2)

theorem fourier5_projector_completeness :
    P_vac5 + P_sym5 + P_anti5 = 1 := by
  unfold P_vac5 P_sym5 P_anti5
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMatrix5, Matrix.mul_apply, pow_succ, Fin.sum_univ_five] <;> ring

theorem fourier5_projector_orthogonality :
    P_sym5 * P_anti5 = 0 := by
  unfold P_sym5 P_anti5
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMatrix5, Matrix.mul_apply, pow_succ, Fin.sum_univ_five] <;> ring

-- 3. Explicit 2x2 SL(2, ℂ) Matrix Generators
def sl2_e : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1],
    ![0, 0]]

def sl2_f : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 0],
    ![1, 0]]

def sl2_h : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0],
    ![0, -1]]

def commutator (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A * B - B * A

theorem sl2_comm_h_e :
    commutator sl2_h sl2_e = (2 : ℂ) • sl2_e := by
  unfold commutator sl2_h sl2_e
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sl2_comm_h_f :
    commutator sl2_h sl2_f = -((2 : ℂ) • sl2_f) := by
  unfold commutator sl2_h sl2_f
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sl2_comm_e_f :
    commutator sl2_e sl2_f = sl2_h := by
  unfold commutator sl2_e sl2_f sl2_h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def sl2_casimir : Matrix (Fin 2) (Fin 2) ℂ :=
  sl2_e * sl2_f + sl2_f * sl2_e + (1 / 2 : ℂ) • (sl2_h * sl2_h)

theorem sl2_casimir_scalar :
    sl2_casimir = (3 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold sl2_casimir sl2_e sl2_f sl2_h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sl2_casimir_comm_e :
    commutator sl2_casimir sl2_e = 0 := by
  rw [sl2_casimir_scalar]
  unfold commutator
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end

end InfoGeometry.Quantum.MatrixFourierSL2Representation
