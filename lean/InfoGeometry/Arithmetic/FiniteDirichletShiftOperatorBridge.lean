import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Dirichlet Shift Operator Bridge

This file establishes the operator-lift edge from the Lapidus-Herichi 
fractal string framework. It bypasses full unbounded normal operators 
by working over a concrete test family of complex exponential functions $e_s(t) = e^{s t}$.
-/

namespace InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge

open scoped BigOperators
open Complex

/-- The vector space of complex-valued functions on the real line. -/
abbrev TestFun := ℝ → ℂ

/-- Continuous scale-translation operator. -/
def shiftOp (u : ℝ) : TestFun →ₗ[ℂ] TestFun where
  toFun f := fun t => f (t - u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftOp_zero : shiftOp 0 = LinearMap.id := by
  ext f t
  simp [shiftOp]

theorem shiftOp_add (u v : ℝ) : shiftOp (u + v) = shiftOp u ∘ₗ shiftOp v := by
  ext f t
  simp [shiftOp, sub_sub]

theorem shiftOp_comp (u v : ℝ) : shiftOp u ∘ₗ shiftOp v = shiftOp (u + v) := by
  ext f t
  simp [shiftOp, sub_sub]

/-- The formal exponential test function. -/
noncomputable def expTestFun (s : ℂ) : TestFun :=
  fun t => Complex.exp (s * (t : ℂ))

/-- Shifting acts diagonally on the exponential test family. -/
theorem shiftOp_expTestFun (u : ℝ) (s : ℂ) :
    shiftOp u (expTestFun s) = Complex.exp (-(s * (u : ℂ))) • expTestFun s := by
  ext t
  simp only [shiftOp, LinearMap.coe_mk, AddHom.coe_mk, expTestFun, Pi.smul_apply, smul_eq_mul]
  have : s * (↑(t - u) : ℂ) = s * (t : ℂ) + -(s * (u : ℂ)) := by push_cast; ring
  rw [this, Complex.exp_add, mul_comm]

/-- Logarithmic shift corresponding to integer $n > 0$. -/
noncomputable def logShiftOp (n : ℕ) : TestFun →ₗ[ℂ] TestFun :=
  shiftOp (Real.log (n : ℝ))

theorem logNatShift_expTestFun (n : ℕ) (s : ℂ) :
    logShiftOp n (expTestFun s) = Complex.exp (-(s * (Real.log (n : ℝ) : ℂ))) • expTestFun s := by
  apply shiftOp_expTestFun

/-- Bridge corollary: complex power is the exponential. -/
theorem complexPow_nat_eq_exp_neg_log (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-s) = Complex.exp (-(s * (Real.log (n : ℝ) : ℂ))) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  rw [Complex.cpow_def_of_ne_zero hn_ne]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (le_of_lt hn_pos)).symm
  rw [hlog]
  ring_nf

/-- The log shift evaluates to $n^{-s}$ via the complex power convention. -/
theorem logShift_exponentialEigen_cpow (n : ℕ) (hn : 0 < n) (s : ℂ) :
    logShiftOp n (expTestFun s) = (n : ℂ) ^ (-s) • expTestFun s := by
  rw [logNatShift_expTestFun]
  rw [complexPow_nat_eq_exp_neg_log n hn s]

/-- Finite Dirichlet shift operator $\sum_{n=1}^N T_{\log n}$. -/
noncomputable def finiteDirichletShiftOp (N : ℕ) : TestFun →ₗ[ℂ] TestFun :=
  ∑ n ∈ Finset.Icc 1 N, logShiftOp n

theorem finiteDirichletShiftOp_expTestFun (N : ℕ) (s : ℂ) :
    finiteDirichletShiftOp N (expTestFun s) = 
      (∑ n ∈ Finset.Icc 1 N, Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))) • expTestFun s := by
  simp [finiteDirichletShiftOp, LinearMap.sum_apply, logNatShift_expTestFun, Finset.sum_smul]

theorem finiteDirichletShift_exponentialTest_cpow (N : ℕ) (s : ℂ) :
    finiteDirichletShiftOp N (expTestFun s) = 
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) • expTestFun s := by
  rw [finiteDirichletShiftOp_expTestFun]
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))) =
        ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn_pos : 0 < n := by
      rw [Finset.mem_Icc] at hn
      exact hn.1
    rw [← complexPow_nat_eq_exp_neg_log n hn_pos s]
  rw [hsum]

end InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
