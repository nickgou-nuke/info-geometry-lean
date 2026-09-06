import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-!
# Section 6: Quantum Structure

Canonical operators identity: (1/2)·Σ_a σ^a·σ^a = 2·I₂
-/

noncomputable section

namespace Section6

open Matrix

def s0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem half_sum_sigma_sq_eq_2I :
    (2 : ℂ)⁻¹ • (s0 * s0 + s1 * s1 + s2 * s2 + s3 * s3) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0, s1, s2, s3, Matrix.smul_apply] <;> ring_nf

end Section6
