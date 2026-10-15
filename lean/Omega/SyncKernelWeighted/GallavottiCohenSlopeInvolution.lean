import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Omega.SyncKernelWeighted.GallavottiCohen

namespace Omega.SyncKernelWeighted

/-- Differentiating the Gallavotti-Cohen pressure duality gives the affine involution satisfied by
the slope observable `α(θ) = P'(θ)`.
    cor:sync-kernel-gc-slope-involution -/
theorem paper_sync_kernel_gc_slope_involution (lam : ℝ → ℝ) (alpha : ℝ → ℝ)
    (hdual : gcPressureDuality lam)
    (hderiv : ∀ theta : ℝ, HasDerivAt (gcPressure lam) (alpha theta) theta) :
    ∀ theta : ℝ, alpha theta + alpha (-theta) = 1 := by
  intro theta
  have h₁ : DifferentiableAt ℝ (gcPressure lam) theta := (hderiv theta).differentiableAt
  have h₂ : DifferentiableAt ℝ (gcPressure lam) (-theta) := (hderiv (-theta)).differentiableAt
  -- Use the known lemma for derivative of f(-x)
  have h₃ : deriv (fun x : ℝ => gcPressure lam (-x)) theta = -deriv (gcPressure lam) (-theta) := by
    rw [deriv_comp_neg (gcPressure lam)]
    <;>
    (try assumption) <;>
    (try simp_all [differentiableAt_id]) <;>
    (try
      {
        -- Show that gcPressure lam is differentiable at -theta
        have h₄ : DifferentiableAt ℝ (gcPressure lam) (-theta) := (hderiv (-theta)).differentiableAt
        exact h₄
      })
  have h₄ : deriv (gcPressure lam) theta = alpha theta := by
    have h₄₁ : HasDerivAt (gcPressure lam) (alpha theta) theta := hderiv theta
    have h₄₂ : deriv (gcPressure lam) theta = alpha theta := h₄₁.deriv
    exact h₄₂
  have h₅ : deriv (gcPressure lam) (-theta) = alpha (-theta) := by
    have h₅₁ : HasDerivAt (gcPressure lam) (alpha (-theta)) (-theta) := hderiv (-theta)
    have h₅₂ : deriv (gcPressure lam) (-theta) = alpha (-theta) := h₅₁.deriv
    exact h₅₂
  have h₆ : deriv (fun x : ℝ => gcPressure lam (-x)) theta = -alpha (-theta) := by
    rw [h₃, h₅]
    <;> ring
  have h₇ : deriv (fun x : ℝ => x + gcPressure lam (-x)) theta = 1 + deriv (fun x : ℝ => gcPressure lam (-x)) theta := by
    have h₇₁ : HasDerivAt (fun x : ℝ => (x : ℝ) + gcPressure lam (-x)) (1 + deriv (fun x : ℝ => gcPressure lam (-x)) theta) theta := by
      have h₇₂ : HasDerivAt (fun x : ℝ => (x : ℝ)) 1 theta := hasDerivAt_id theta
      have h₇₃ : HasDerivAt (fun x : ℝ => gcPressure lam (-x)) (deriv (fun x : ℝ => gcPressure lam (-x)) theta) theta := by
        have h₇₄ : DifferentiableAt ℝ (fun x : ℝ => gcPressure lam (-x)) theta := by
          -- Prove differentiability of x ↦ gcPressure lam (-x)
          have h₇₅ : DifferentiableAt ℝ (fun x : ℝ => -x) theta := differentiableAt_id.neg
          have h₇₆ : DifferentiableAt ℝ (gcPressure lam) (-theta) := (hderiv (-theta)).differentiableAt
          exact h₇₆.comp theta h₇₅
        have h₇₇ : HasDerivAt (fun x : ℝ => gcPressure lam (-x)) (deriv (fun x : ℝ => gcPressure lam (-x)) theta) theta :=
          h₇₄.hasDerivAt
        exact h₇₇
      have h₇₈ : HasDerivAt (fun x : ℝ => (x : ℝ) + gcPressure lam (-x)) (1 + deriv (fun x : ℝ => gcPressure lam (-x)) theta) theta := HasDerivAt.add h₇₂ h₇₃
      exact h₇₈
    have h₇₉ : deriv (fun x : ℝ => x + gcPressure lam (-x)) theta = 1 + deriv (fun x : ℝ => gcPressure lam (-x)) theta := by
      apply HasDerivAt.deriv
      exact h₇₁
    exact h₇₉
  have h₈ : deriv (fun x : ℝ => x + gcPressure lam (-x)) theta = 1 + -alpha (-theta) := by
    calc
      deriv (fun x : ℝ => x + gcPressure lam (-x)) theta = 1 + deriv (fun x : ℝ => gcPressure lam (-x)) theta := h₇
      _ = 1 + -alpha (-theta) := by rw [h₆] <;> ring
  have h₉ : deriv (gcPressure lam) theta = 1 + -alpha (-theta) := by
    have h₉₁ : (fun x : ℝ => x + gcPressure lam (-x)) = (gcPressure lam) := by
      funext x
      have h₉₂ := hdual x
      linarith
    have h₉₂ : deriv (fun x : ℝ => x + gcPressure lam (-x)) theta = deriv (gcPressure lam) theta := by
      rw [h₉₁]
    linarith
  have h₁₀ : alpha theta = 1 + -alpha (-theta) := by
    linarith
  linarith

end Omega.SyncKernelWeighted