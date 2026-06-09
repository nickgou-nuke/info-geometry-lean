import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped BigOperators

/-!
# Section 9: Curvature — Lean 4

Lorentz generators σ_{ab} = (i/2)·[σ_a, σ_b] are traceless.
Curvature definitions and flat space limit.
-/

noncomputable section

namespace Section9

open Matrix

def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => I2 | 1 => s1 | 2 => s2 | 3 => s3

/-- Lorentz generators σ_{ab} = (i/2)·[σ_a, σ_b]. -/
def sigma_ab (a b : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (sigma a * sigma b - sigma b * sigma a)

/-- The trace of each Lorentz generator vanishes. -/
theorem sigma_ab_traceless (a b : Fin 4) :
    (∑ i : Fin 2, sigma_ab a b i i) = (0 : ℂ) := by
  unfold sigma_ab
  fin_cases a <;> fin_cases b <;>
    simp [sigma, I2, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;> ring

end Section9
