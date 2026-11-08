import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic

open Matrix

namespace InfoGeometry.Topology.FibonacciFR

/-- The exact root of unity limits and constants for the Fibonacci anyon field -/
structure FibonacciData where
  z : ℂ
  s : ℂ
  z_eq : z^4 - z^3 + z^2 - z + 1 = 0
  s_sq : s^2 = z - z^4 - 1

/-- Inverse golden ratio `phi_inv` -/
def FibonacciData.phi_inv (D : FibonacciData) : ℂ := D.z - D.z^4 - 1

/-- Root of unity phases for the braiding matrix -/
def FibonacciData.R_phase_1 (D : FibonacciData) : ℂ := D.z^6
def FibonacciData.R_phase_2 (D : FibonacciData) : ℂ := D.z^3

/-- F matrix: the topological fusion matrix -/
noncomputable def F_matrix (D : FibonacciData) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![D.phi_inv, D.s],
    ![D.s, -D.phi_inv]]

/-- R matrix: the topological braiding matrix -/
noncomputable def R_matrix (D : FibonacciData) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![D.R_phase_1, 0],
    ![0, D.R_phase_2]]

end InfoGeometry.Topology.FibonacciFR
