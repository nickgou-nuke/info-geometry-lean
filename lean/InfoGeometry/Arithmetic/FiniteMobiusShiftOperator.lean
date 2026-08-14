import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperator

/-!
# Finite Möbius shift operator

This is the finite Möbius-weighted companion of the Dirichlet shift operator.
It records the coefficient-level shadow of `1 / ζ(∂)` on exponential test
functions, without asserting an infinite inverse or any functional calculus.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteMobiusShiftOperator

open scoped BigOperators
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperator

def finiteMobiusShift (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) *
      logScaleTranslation (Real.log (n : ℝ)) f t

theorem finiteMobiusShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteMobiusShift N (exponentialTest s) t =
      (∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius n : ℂ) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) *
        exponentialTest s t := by
  unfold finiteMobiusShift
  simp_rw [logScaleTranslation_exponentialTest]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end InfoGeometry.Arithmetic.FiniteMobiusShiftOperator
