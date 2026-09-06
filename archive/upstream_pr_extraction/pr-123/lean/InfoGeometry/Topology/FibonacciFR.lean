import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

open Matrix

namespace InfoGeometry.Topology.FibonacciFR

/- The exact root of unity limits and constants for the Fibonacci anyon field. -/
def FibonacciData : Type :=
  {p : ℂ × ℂ //
    p.1 ^ 4 - p.1 ^ 3 + p.1 ^ 2 - p.1 + 1 = 0 ∧
      p.2 ^ 2 = p.1 - p.1 ^ 4 - 1}

namespace FibonacciData

abbrev z (D : FibonacciData) : ℂ := D.1.1
abbrev s (D : FibonacciData) : ℂ := D.1.2

theorem z_eq (D : FibonacciData) :
    D.z ^ 4 - D.z ^ 3 + D.z ^ 2 - D.z + 1 = 0 :=
  D.2.1

theorem s_sq (D : FibonacciData) :
    D.s ^ 2 = D.z - D.z ^ 4 - 1 :=
  D.2.2

end FibonacciData

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
