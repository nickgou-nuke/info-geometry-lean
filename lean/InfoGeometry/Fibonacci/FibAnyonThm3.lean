import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix
open Complex
open Real

namespace InfoGeometry.Fibonacci.FibAnyonThm3

noncomputable section

/-! Theorem 3: R-Matrix -/

noncomputable def q : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I / 5)

theorem q_fifth_power : q^5 = 1 := by
  calc
    q^5 = (Complex.exp (2 * (π : ℂ) * Complex.I / 5)) ^ 5 := rfl
    _ = Complex.exp ((2 * (π : ℂ) * Complex.I / 5) * (5 : ℂ)) := by
      rw [← Complex.exp_nat_mul, mul_comm, Nat.cast_ofNat]
    _ = Complex.exp (2 * (π : ℂ) * Complex.I) := by ring_nf
    _ = Complex.cos (2 * (π : ℂ)) + Complex.sin (2 * (π : ℂ)) * Complex.I := by
      rw [Complex.exp_mul_I]
    _ = 1 := by simp

lemma q_ne_zero : q ≠ 0 := Complex.exp_ne_zero _

def R : Matrix (Fin 2) (Fin 2) ℂ :=
  !![q^(-4 : ℤ), 0;
     0, q^3]

theorem R_det : R.det = q⁻¹ := by
  simp [R, Matrix.det_fin_two]
  field_simp [q_ne_zero]

theorem R_char_poly_zero : (R - (q^(-4 : ℤ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
                          (R - (q^3) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

end

end InfoGeometry.Fibonacci.FibAnyonThm3
