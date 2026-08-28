import Mathlib
import InfoGeometry.Physics.SolovievProjectedParameterBridge

noncomputable section

namespace InfoGeometry.Physics.NuclearFiniteCARProjection

open Matrix
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievProjectedParameterBridge

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def annihilation : M2R := !![0, 1; 0, 0]

def creation : M2R := !![0, 0; 1, 0]

def number : M2R := creation * annihilation

def oneModeHamiltonian (epsilon : ℝ) : M2R := epsilon • number

theorem annihilation_sq : annihilation * annihilation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilation, Matrix.mul_apply, Fin.sum_univ_two]

theorem creation_sq : creation * creation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [creation, Matrix.mul_apply, Fin.sum_univ_two]

theorem car_anticommutator :
    annihilation * creation + creation * annihilation = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilation, creation]

theorem number_eq_diagonal : number = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [number, creation, annihilation, Matrix.mul_apply, Fin.sum_univ_two]

theorem number_idempotent : number * number = number := by
  rw [number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem oneModeHamiltonian_eq_block (epsilon : ℝ) :
    oneModeHamiltonian epsilon = blockHamiltonian 0 epsilon 0 := by
  rw [oneModeHamiltonian, number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockHamiltonian]

theorem oneMode_parameters_reconstruct (epsilon : ℝ) :
    blockHamiltonian (qpEnergy (oneModeHamiltonian epsilon))
      (phononEnergy (oneModeHamiltonian epsilon))
      (coupling (oneModeHamiltonian epsilon)) =
      oneModeHamiltonian epsilon := by
  apply projected_parameter_reconstruction
  rw [oneModeHamiltonian_eq_block]
  rfl

end InfoGeometry.Physics.NuclearFiniteCARProjection
