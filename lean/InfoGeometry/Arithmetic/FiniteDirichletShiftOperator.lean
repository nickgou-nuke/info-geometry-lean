import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Dirichlet shift operator

This is the finite operator shadow of the logarithmic-scale identity
`n^(-s) = exp (-s log n)`.  It acts on exponential test functions only;
no unbounded operator, spectrum, functional calculus, or infinite series is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteDirichletShiftOperator

open scoped BigOperators

def logScaleTranslation (h : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => f (t - h)

def exponentialTest (s : ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (s * (t : ℂ))

def finiteDirichletShift (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∑ n ∈ Finset.Icc 1 N, logScaleTranslation (Real.log (n : ℝ)) f t

theorem logScaleTranslation_exponentialTest (s : ℂ) (h t : ℝ) :
    logScaleTranslation h (exponentialTest s) t =
      Complex.exp (-s * (h : ℂ)) * exponentialTest s t := by
  unfold logScaleTranslation exponentialTest
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem finiteDirichletShift_exponentialTest (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (exponentialTest s) t =
      (∑ n ∈ Finset.Icc 1 N,
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) * exponentialTest s t := by
  unfold finiteDirichletShift
  simp_rw [logScaleTranslation_exponentialTest]
  rw [Finset.sum_mul]

theorem finiteDirichletShift_exponentialTest_cpow (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (exponentialTest s) t =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) * exponentialTest s t := by
  rw [finiteDirichletShift_exponentialTest]
  apply congrArg (fun a : ℂ => a * exponentialTest s t)
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn1))
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    have hnonneg : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
    exact (Complex.ofReal_log hnonneg).symm
  rw [Complex.cpow_def_of_ne_zero hn0, hlog]
  ring_nf

end InfoGeometry.Arithmetic.FiniteDirichletShiftOperator
