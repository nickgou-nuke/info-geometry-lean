import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Biquaternion Laplace Resolvent

Formalizes the algebraic resolvent identity for the biquaternion exponential.
This maps the continuous conformal scaling group into the discrete 
scale parameters `s` via the Matrix Laplace Transform:
`L{exp(tX)}(s) = (sI - X)⁻¹`
-/

namespace BiquaternionLaplaceResolvent

open Matrix

/-- A biquaternion operator `X` constructed from scalar `a₀` and vector 
part `(a₁, a₂, a₃)` using the Pauli matrix basis. -/
def X (a0 a1 a2 a3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a0 + a3, a1 - Complex.I * a2; 
     a1 + Complex.I * a2, a0 - a3]

/-- The magnitude squared of the vector part. -/
def v_sq (a1 a2 a3 : ℂ) : ℂ :=
  a1^2 + a2^2 + a3^2

/-- The inverse operator `(sI - X)` for the Laplace transform. -/
def sI_minus_X (s a0 a1 a2 a3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  s • (1 : Matrix (Fin 2) (Fin 2) ℂ) - X a0 a1 a2 a3

/-- 
Theorem: The determinant of `(sI - X)` exactly equals `(s - a₀)² - v²`.
This provides the characteristic polynomial and establishes the 
tripotent poles of the resolvent when evaluated.
-/
theorem resolvent_det (s a0 a1 a2 a3 : ℂ) :
    (sI_minus_X s a0 a1 a2 a3).det = (s - a0)^2 - v_sq a1 a2 a3 := by
  dsimp [sI_minus_X, X, v_sq, det]
  have hI : Complex.I * Complex.I = -1 := Complex.I_sq
  calc
    _ = (s - (a0 + a3)) * (s - (a0 - a3)) - (- (a1 - Complex.I * a2)) * (- (a1 + Complex.I * a2)) := rfl
    _ = (s - a0)^2 - a3^2 - (a1^2 - (Complex.I * a2)^2) := by ring
    _ = (s - a0)^2 - a3^2 - a1^2 + Complex.I^2 * a2^2 := by ring
    _ = (s - a0)^2 - a3^2 - a1^2 + (-1) * a2^2 := by rw [hI]
    _ = (s - a0)^2 - (a1^2 + a2^2 + a3^2) := by ring

/-- The analytical Adjugate matrix (numerator of the resolvent). 
    It equals `(s - a₀)I + a·σ`. -/
def Adjugate (s a0 a1 a2 a3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (s - a0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + 
  !![a3, a1 - Complex.I * a2; 
     a1 + Complex.I * a2, -a3]

/-- 
Theorem: The analytical Adjugate multiplied by `(sI - X)` perfectly 
yields the determinant scalar matrix. 

This proves that `(sI - X)⁻¹ = [(s - a₀)I + a·σ] / [(s - a₀)² - v²]`.
This resolvent algebraically traps the non-invertible zero-modes 
(topological defects) and physical poles of the bulk string!
-/
theorem resolvent_identity (s a0 a1 a2 a3 : ℂ) :
    sI_minus_X s a0 a1 a2 a3 * Adjugate s a0 a1 a2 a3 = 
    ((s - a0)^2 - v_sq a1 a2 a3) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  have hI : Complex.I * Complex.I = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [sI_minus_X, X, Adjugate, v_sq, Matrix.mul_apply, Fin.sum_univ_two, 
          smul_apply, add_apply, sub_apply, one_val] <;>
    try {
      calc
        _ = (s - a0)^2 - a3^2 - a1^2 + Complex.I^2 * a2^2 := by ring
        _ = (s - a0)^2 - a3^2 - a1^2 + (-1) * a2^2 := by rw [hI]
        _ = (s - a0)^2 - a1^2 - a2^2 - a3^2 := by ring
    }
  <;> ring

end BiquaternionLaplaceResolvent
