import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic

/-!
# Euler coordinates and meromorphic divisor readouts

This owner contains the theorem-safe analytic core of the Euler/logarithmic
bridge.  It keeps the configuration-space Euler derivative distinct from the
spectral logarithmic derivative.  Meromorphic divisor data are read through
Mathlib's `meromorphicOrderAt`; no analytic continuation or zero-location
claim for the Riemann zeta function is introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaEulerLaurentMonodromy

/-! ## Euler dilation in logarithmic coordinates -/

def logarithmicCoordinate (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  f (Real.exp y)

theorem hasDerivAt_logarithmicCoordinate
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (y : ℝ)
    (hf : HasDerivAt f (f' (Real.exp y)) (Real.exp y)) :
    HasDerivAt (logarithmicCoordinate f) (Real.exp y * f' (Real.exp y)) y := by
  simpa [logarithmicCoordinate, mul_comm] using
    hf.comp y (Real.hasDerivAt_exp y)

theorem deriv_logarithmicCoordinate
    (f : ℝ → ℝ) (y : ℝ)
    (hf : DifferentiableAt ℝ f (Real.exp y)) :
    deriv (logarithmicCoordinate f) y =
      Real.exp y * deriv f (Real.exp y) := by
  exact (hasDerivAt_logarithmicCoordinate f (fun x => deriv f x) y
    (hf.hasDerivAt)).deriv

theorem eulerDerivative_readout
    (f : ℝ → ℝ) (y : ℝ)
    (hf : DifferentiableAt ℝ f (Real.exp y)) :
    deriv (logarithmicCoordinate f) y =
      Real.exp y * deriv f (Real.exp y) :=
  deriv_logarithmicCoordinate f y hf

/-! ## Native meromorphic divisor factorization -/

theorem meromorphicOrderAt_local_factorization
    {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a)
    (hfinite : meromorphicOrderAt f a ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g a ∧
        g a ≠ 0 ∧
        ∀ᶠ z in nhdsWithin a {a}ᶜ,
          f z = (z - a) ^ (meromorphicOrderAt f a).untop₀ • g z := by
  exact (meromorphicOrderAt_ne_top_iff hf).mp hfinite

theorem meromorphicOrderAt_is_zero_of_local_factorization
    {f g : ℂ → ℂ} {a : ℂ} {m : ℤ}
    (hf : MeromorphicAt f a)
    (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0)
    (hfactor : ∀ᶠ z in nhdsWithin a {a}ᶜ,
      f z = (z - a) ^ m • g z) :
    meromorphicOrderAt f a = m := by
  exact (meromorphicOrderAt_eq_int_iff hf).2 ⟨g, hg, hga, hfactor⟩

/-! ## Logarithmic derivative readouts away from the divisor -/

theorem logDeriv_mul_readout
    {f g : ℂ → ℂ} {z : ℂ}
    (hfz : f z ≠ 0) (hgz : g z ≠ 0)
    (hfd : DifferentiableAt ℂ f z) (hgd : DifferentiableAt ℂ g z) :
    logDeriv (fun w => f w * g w) z =
      logDeriv f z + logDeriv g z := by
  exact logDeriv_mul z hfz hgz hfd hgd

theorem logDeriv_zpow_readout (z : ℂ) (m : ℤ) :
    logDeriv (fun w : ℂ => w ^ m) z = (m : ℂ) / z := by
  exact logDeriv_zpow z m

theorem logDeriv_local_factor_readout
    {g : ℂ → ℂ} {a z : ℂ} {m : ℤ}
    (hza : z - a ≠ 0) (hgz : g z ≠ 0)
    (hgd : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (w - a) ^ m * g w) z =
      (m : ℂ) / (z - a) + logDeriv g z := by
  have hpow : (z - a) ^ m ≠ 0 := zpow_ne_zero _ hza
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w - a) z := by fun_prop
  have hpowd' : DifferentiableAt ℂ (fun u : ℂ => u ^ m) (z - a) :=
    differentiableAt_zpow.2 (Or.inl hza)
  have hpowd : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ m) z := by
    simpa only [Function.comp_apply] using hpowd'.comp z hshift
  rw [logDeriv_mul z hpow hgz hpowd hgd]
  rw [logDeriv_fun_zpow hshift m]
  simp [logDeriv_apply, div_eq_mul_inv]

end InfoGeometry.Arithmetic.ZetaEulerLaurentMonodromy

end noncomputable section
