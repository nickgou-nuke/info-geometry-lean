import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.SuperchargeAlgebra

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [Ring R]

def SuperHamiltonian (N_B N_F : R) (E_0 : R) : R :=
  N_B + N_F + E_0

def Anticommutator (A B : R) : R :=
  A * B + B * A

def NilpotentSquare (Q : R) : Prop :=
  Q * Q = 0

theorem supercharge_nilpotent_of_square_zero (a_dag f : R) (hf : f * f = 0)
    (h_comm : f * a_dag = a_dag * f) :
    NilpotentSquare (a_dag * f) := by
  unfold NilpotentSquare
  calc (a_dag * f) * (a_dag * f)
    _ = a_dag * (f * (a_dag * f)) := by rw [← mul_assoc a_dag f (a_dag * f)]
    _ = a_dag * ((f * a_dag) * f) := by rw [← mul_assoc f a_dag f]
    _ = a_dag * ((a_dag * f) * f) := by rw [h_comm]
    _ = a_dag * (a_dag * (f * f)) := by rw [mul_assoc a_dag f f]
    _ = a_dag * (a_dag * 0) := by rw [hf]
    _ = 0 := by simp

theorem super_hamiltonian_vacuum_energy (E_0 : R) :
    SuperHamiltonian 0 0 E_0 = E_0 := by
  unfold SuperHamiltonian
  simp

theorem grand_supercharge_algebra_synthesis (a_dag f : R) (E_0 : R)
    (hf : f * f = 0) (h_comm : f * a_dag = a_dag * f) :
    (NilpotentSquare (a_dag * f)) ∧
    (SuperHamiltonian 0 0 E_0 = E_0) :=
  ⟨supercharge_nilpotent_of_square_zero a_dag f hf h_comm,
   super_hamiltonian_vacuum_energy E_0⟩

end InfoGeometry.Quantum.SuperchargeAlgebra
