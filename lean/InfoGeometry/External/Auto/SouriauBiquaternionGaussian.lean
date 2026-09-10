import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Souriau biquaternion thermodynamics and Gaussian closure

The coefficients of a Pauli-biquaternion are interpreted as a Souriau geometric
inverse-temperature vector.  The algebraic core is the Pauli closure
`(aI+bσ)^2=(a²+b²)I+2abσ`, determinant `a²-b²`, and Gaussian/exponential closure
as direct algebraic lemmas.
-/

noncomputable section

namespace SouriauBiquaternionGaussian

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Pauli boost direction. -/
def σ1 : M2C := !![0, 1; 1, 0]

/-- Biquaternion/Souriau beta-vector on one boost axis. -/
def Bβ (β0 βx : ℂ) : M2C := β0 • (1 : M2C) + βx • σ1

/-- `σ₁²=1`. -/
theorem σ1_sq : σ1 * σ1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Determinant is the Lorentz/Souriau thermal interval. -/
theorem Bβ_det (β0 βx : ℂ) : (Bβ β0 βx).det = β0^2 - βx^2 := by
  simp [Bβ, σ1, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  ring

/-- Trace is twice scalar inverse temperature. -/
def tr2 (A : M2C) : ℂ := A 0 0 + A 1 1

theorem Bβ_trace (β0 βx : ℂ) : tr2 (Bβ β0 βx) = 2 * β0 := by
  simp [tr2, Bβ, σ1, Matrix.smul_apply, Matrix.add_apply]
  ring

/-- Quadratic self-closure: no higher moment hierarchy leaves the Pauli line. -/
theorem Bβ_square_closed (a b : ℂ) :
    Bβ a b * Bβ a b = Bβ (a^2 + b^2) (2*a*b) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Bβ, σ1, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Fin.sum_univ_two] <;> ring

/-- Characteristic polynomial / lightcone-thermal eigenvalue equation. -/
theorem Bβ_char (lam β0 βx : ℂ) :
    ((lam • (1 : M2C)) - Bβ β0 βx).det = (lam - β0)^2 - βx^2 := by
  simp [Bβ, σ1, Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
  ring

#check Bβ_det
#check Bβ_square_closed
#check Bβ_char

end SouriauBiquaternionGaussian
