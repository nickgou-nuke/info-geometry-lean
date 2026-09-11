import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The real hyperbolic dilatation identity

This file records the scalar part of the proposed quasiconformal/Bogoliubov
bridge.  The analytic carrier is the real function `tanh`; no claim about a
Beltrami equation is made here.  Such a claim needs a map and differentiability
data in addition to a scalar parameter.
-/

namespace InfoGeometry.Analysis

noncomputable section

def beltramiMagnitude (r : ℝ) : ℝ := Real.tanh r

def maximalDilatation (μ : ℝ) : ℝ := (1 + μ) / (1 - μ)

@[simp] theorem beltramiMagnitude_def (r : ℝ) :
    beltramiMagnitude r = Real.tanh r := rfl

theorem beltramiMagnitude_lt_one (r : ℝ) :
    |beltramiMagnitude r| < 1 := by
  simp [beltramiMagnitude, abs_lt]
  exact ⟨Real.neg_one_lt_tanh r, Real.tanh_lt_one r⟩

theorem one_sub_beltramiMagnitude_ne_zero (r : ℝ) :
    1 - beltramiMagnitude r ≠ 0 := by
  have hlt := beltramiMagnitude_lt_one r
  linarith [le_abs_self (beltramiMagnitude r)]

theorem maximalDilatation_tanh (r : ℝ) :
    maximalDilatation (beltramiMagnitude r) = Real.exp (2 * r) := by
  rw [maximalDilatation, beltramiMagnitude]
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh r ≠ 0 := ne_of_gt (Real.cosh_pos r)
  field_simp [hc]
  rw [Real.cosh_add_sinh, Real.cosh_sub_sinh]
  rw [← Real.exp_add]
  ring_nf

theorem maximalDilatation_pos (r : ℝ) :
    0 < maximalDilatation (beltramiMagnitude r) := by
  rw [maximalDilatation]
  have hμ := beltramiMagnitude_lt_one r
  have hμ' := (abs_lt.mp hμ)
  have hnum : 0 < 1 + beltramiMagnitude r := by linarith
  have hden : 0 < 1 - beltramiMagnitude r := by linarith
  exact div_pos hnum hden

theorem maximalDilatation_eq_exp_two_mul (r : ℝ) :
    maximalDilatation (beltramiMagnitude r) = Real.exp (2 * r) :=
  maximalDilatation_tanh r

end
end InfoGeometry.Analysis
