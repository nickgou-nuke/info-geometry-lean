import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Two-channel Andreev mixing example

This module defines a real two-channel rotation and proves its equal-amplitude
output at angle `π / 4`. It does not model a BdG boundary-value problem or
establish a Majorana zero mode, a topological invariant, or a relation to the
nuclear scalar triple-product model.
-/

noncomputable section

namespace InfoGeometry.Nuclear.AndreevMajoranaBridge

open Matrix

/-- Real two-channel rotation used as a finite mixing example. -/
def andreev_s_matrix (alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos alpha, -Real.sin alpha; 
     Real.sin alpha,  Real.cos alpha]

/-- A pure incoming electron from the lead before entering the distributed interface. -/
def pure_electron : Fin 2 → ℝ := ![1, 0]

/-- The two real coordinates have equal amplitude. -/
def equal_amplitude (psi : Fin 2 → ℝ) : Prop :=
  psi 0 = psi 1

/-! At `π / 4`, the rotation sends the first basis vector to equal real
coordinates. This finite matrix fact alone has no Majorana-mode conclusion. -/
theorem andreev_rotation_equal_amplitude_at_pi_over_4 :
    equal_amplitude (mulVec (andreev_s_matrix (Real.pi / 4)) pure_electron) := by
  simp [equal_amplitude, andreev_s_matrix, pure_electron,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Real.sin_pi_div_four, Real.cos_pi_div_four]

end InfoGeometry.Nuclear.AndreevMajoranaBridge
