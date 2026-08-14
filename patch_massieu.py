import re

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanMassieuConvexity.lean', 'r') as f:
    text = f.read()

# Add import
if 'import Mathlib.Analysis.Calculus.ContDiff.Deriv' not in text:
    text = text.replace('import Mathlib.Analysis.Calculus.Deriv.Comp', 'import Mathlib.Analysis.Calculus.Deriv.Comp\nimport Mathlib.Analysis.Calculus.ContDiff.Deriv')

lemmas = """
theorem deriv_shift_zero {f : ℝ → ℝ} (t : ℝ) (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => f (t + s)) 0 = deriv f t := by
  have hd1 : HasDerivAt f (deriv f t) (t + 0) := by
    rw [add_zero]
    exact hf.hasDerivAt
  have hd2 : HasDerivAt (fun s => t + s) 1 0 := by
    apply HasDerivAt.const_add
    exact hasDerivAt_id 0
  have hc := HasDerivAt.comp 0 hd1 hd2
  rw [mul_one] at hc
  exact hc.deriv

theorem deriv_shift {f : ℝ → ℝ} (t : ℝ) (s : ℝ) (hf : DifferentiableAt ℝ f (t + s)) :
    deriv (fun s' => f (t + s')) s = deriv f (t + s) := by
  have hd1 : HasDerivAt f (deriv f (t + s)) (t + s) := hf.hasDerivAt
  have hd2 : HasDerivAt (fun s' => t + s') 1 s := by
    apply HasDerivAt.const_add
    exact hasDerivAt_id s
  have hc := HasDerivAt.comp s hd1 hd2
  rw [mul_one] at hc
  exact hc.deriv

theorem second_deriv_shift {f : ℝ → ℝ} (t : ℝ)
    (hf : ContDiff ℝ 2 f) :
    deriv^[2] f t = deriv (fun s => deriv (fun s' => f (t + s')) s) 0 := by
  change deriv (deriv f) t = deriv (fun s => deriv (fun s' => f (t + s')) s) 0
  have h_inner (s : ℝ) : deriv (fun s' => f (t + s')) s = deriv f (t + s) := by
    apply deriv_shift
    have h1 := hf.differentiable (by norm_num)
    exact h1 (t + s)
  have h_outer : (fun s => deriv (fun s' => f (t + s')) s) = (fun s => deriv f (t + s)) := by
    ext s
    exact h_inner s
  rw [h_outer]
  apply (deriv_shift_zero t _).symm
  have hd := hf.differentiable_deriv_two
  exact hd t

theorem souriauMassieu_strictlyConvex_along_lines"""

text = text.replace('theorem souriauMassieu_strictlyConvex_along_lines', lemmas)

target_hs2 = """  have hs2 : deriv^[2] (logSumExp w a) t = deriv (fun s => deriv (fun s' => logSumExp w a (t + s')) s) 0 := by
    simpa [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      (logSumExp_secondDeriv_eq_variance w a hw t)"""

replacement_hs2 = """  have hs2 : deriv^[2] (logSumExp w a) t = deriv (fun s => deriv (fun s' => logSumExp w a (t + s')) s) 0 := by
    exact second_deriv_shift t hf_contDiff"""

text = text.replace(target_hs2, replacement_hs2)

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanMassieuConvexity.lean', 'w') as f:
    f.write(text)

